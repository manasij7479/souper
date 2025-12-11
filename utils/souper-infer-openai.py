import sys
import os
import subprocess
import argparse
import redis
import time
import tempfile
import random
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError
from openai import AzureOpenAI
from openai import APIConnectionError, RateLimitError, APIError
from types import SimpleNamespace
import logging

logger = logging.getLogger("souper.infer")

# Timeout (in seconds) for all invocations of the souper-check binary
S_CHECK_TIMEOUT_SECONDS = 120

# Default architectures for profit calculation
DEFAULT_ARCHITECTURES = ["x86-64", "aarch64", "riscv64", "souperir"]

client = AzureOpenAI(
  api_key=os.environ.get("OPENAI_API_KEY"),
  api_version="2024-02-15-preview",
  azure_endpoint="https://llm-proxy.perflab.nvidia.com",
)

def call_openai_with_retry(func, max_retries=5, initial_delay=1.0, max_delay=60.0, request_timeout=60.0, debug=False):
  """
  Call OpenAI API with exponential backoff retry logic.
  
  Args:
    func: Function to call (should return the API response)
    max_retries: Maximum number of retry attempts
    initial_delay: Initial delay in seconds
    max_delay: Maximum delay in seconds
    debug: Whether to print debug information
  
  Returns:
    API response or raises the last exception
  """
  for attempt in range(max_retries + 1):
    if debug:
      logger.debug("openai attempt=%d/%d timeout=%ss", attempt + 1, max_retries + 1, request_timeout)
    try:
      if request_timeout and request_timeout > 0:
        with ThreadPoolExecutor(max_workers=1) as executor:
          future = executor.submit(func)
          return future.result(timeout=request_timeout)
      else:
        return func()
    except FuturesTimeoutError as e:
      if attempt == max_retries:
        raise TimeoutError(f"OpenAI API request timed out after {request_timeout}s")
      delay = min(initial_delay * (2 ** attempt), max_delay)
      jitter = random.uniform(0.1, 0.3) * delay
      total_delay = delay + jitter
      if debug:
        logger.warning("openai timeout attempt=%d/%d retry_in=%.2fs err=%s", attempt + 1, max_retries + 1, total_delay, e)
      time.sleep(total_delay)
    except (APIConnectionError, RateLimitError) as e:
      if attempt == max_retries:
        # Last attempt failed, re-raise the exception
        raise e
      
      # Calculate delay with exponential backoff and jitter
      delay = min(initial_delay * (2 ** attempt), max_delay)
      jitter = random.uniform(0.1, 0.3) * delay
      total_delay = delay + jitter
      
      if debug:
        logger.warning("openai transient error attempt=%d/%d retry_in=%.2fs err=%s", attempt + 1, max_retries + 1, total_delay, e)
      
      time.sleep(total_delay)
    except APIError as e:
      # Retry once for specific 400 error where a message content is empty
      msg = str(e)
      status_code = getattr(e, 'status_code', None)
      if status_code == 400 and "least 1 character" in msg:
        if attempt < 1:
          if debug:
            logger.warning("openai 400 empty-content; retrying once err=%s", e)
          time.sleep(0.5)
          continue
      # For other API errors, don't retry
      if debug:
        logger.error("openai API error (no retry) err=%s", e)
      raise e

log=[{
"role": "system",
"content":
"""
You are an expert compiler engineer.
Given a piece of SSA code representing a function to infer (optimize),
you have to generate a replacement.
The replacement can not be the same as the SSA value being optimized, it should
be a simpler value that is faster to compute but still produce the same result
for all possible inputs.
Name of SSA variables are prefixed with %.
A pc is a boolean precondition that implies a valid optimization.
The syntax is: pc %0 1, means that the optimization is valid when %%0 is 1.
The pc does not count towards the cost of the input or the profitability of the optimization.

The operations available are:
add, sub, mul, udiv, sdiv, udivexact, sdivexact,
urem, srem, and, or, xor, shl, , lshr, lshrexact, ashr, ashrexact, select, zext, sext, trunc, eq,
ne, ult, slt, ule, sle, ctpop, bswap, bitreverse, cttz, ctlz, fshl, fshr", extractvalue, sadd.with.overflow,
uadd.with.overflow, ssub.with.overflow, usub.with.overflow, smul.with.overflow, umul.with.overflow, sadd.sat, uadd.sat,
ssub.sat, usub.sat.
The operations are named after the LLVM IR operations they represent, with the usual semantics.

Do not explain the optimizations, just generate the replacement.
Do not regenerate the existing infer command.
Do not start a line with a variable that has already been defined.
Do not declare new variables.
Do not generate more operations than necessary.
Try to generate the simplest replacement possible.
If the input is equivalent to a constant, the replacement should be that constant.
Try to come up with new constants in the result by combining existing ones with arithmetic operations.
Avoid using the same constant in the replacement as the original.
Avoid using the poison versions of the operations unless necessary for the optimization to be valid.
Make sure the generated replacement is well-formed and well-typed.
Make sure the generated replacement does not introduce a new path condition (pc).
If nothing else works, try elementary algebraic operations on the variables.

Most operations cost 1.
bitreverse, bswap, ctpop, cttz, ctlz, udiv, sdiv, urem, srem cost 5.
fshl, fshr, select cost 3.
The profitability of an optimization is the cost of the original expression minus the cost of the replacement.
The goal is to maximize the profitability by eliminating costlier operations and replacing them with cheaper ones.

eq, ne, ult, slt, ule, sle return a 1 bit result.
zext, sext, trunc change the width of the result.
select returns the type of the second and third arguments.

Here are some complete examples to illustrate the syntax:

%0:i32 = var ; 0
%1:i32 = and 1603:i32, %0
%2:i32 = and 1:i32, %1
infer %2
%3:i32 = and 1:i32, %0
result %3

%0:i64 = var ; 0
%1:i64 = add 28:i64, %0
%2:i64 = mul 1:i64, %1
infer %2
result %1

%v0:i8 = var ; v0
%1:i8 = lshr %v0, 3:i8
%2:i8 = and 1:i8, %1
%3:i8 = mul 8:i8, %2
infer %3
%4:i8 = and 8:i8, %v0
result %4

%0:i32 = var
%1:i1 = ne 0:i32, %0
%2:i32 = select %1, 1:i32, 0:i32
infer %2
%3:i32 = zext %1
result %3

%0:i64 = var
%1:i64 = mul 8:i64, %0
infer %1
%2:i64 = shl %0, 3:i64
result %2

%0:i32 = var
%1:i32 = urem %0, 32:i32
infer %1
%2:i32 = and 31:i32, %0
result %2

%0:i16 = var
%1:i32 = zext %0
%2:i32 = and 64512:i32, %1
%3:i1 = eq 55296:i32, %2
%4:i1 = select %3, 1:i1, 0:i1
infer %4
%5:i16 = and 64512:i16, %0
%6:i1 = eq 55296:i16, %5
result %6

%v0:i8 = var ; v0
%1:i8 = ctpop %v0
%2:i1 = ult 7:i8, %1
infer %2
%3:i1 = eq 255:i8, %v0
result %3

%0:i32 = var
%1:i32 = shl 1:i32, %0
%2:i32 = and 544:i32, %1
%3:i1 = eq 0:i32, %2
infer %3
%4:i32 = shl 4223401984:i32, %0
%5:i1 = slt %4, %0
result %5

%0:i32 = var
%1:i32 = var
%2:i32 = or %0, %1
%3:i32 = and 1:i32, %2
%4:i32 = and 4294967294:i32, %0
%5:i32 = or %3, %4
infer %5
%6:i32 = and 1:i32, %1
%7:i32 = or %0, %6
result %7

%0:i32 = var
%1:i1 = var
%2:i32 = select %1, 8:i32, 1:i32
%3:i32 = udiv %0, %2
infer %3
%4:i32 = select %1, 3:i32, 0:i32
%5:i32 = lshr %0, %4
result %5

%0:i64 = var
%1:i64 = add 1:i64, %0 (hasExternalUses)
%2:i64 = var
%3:i1 = ult %1, %2
pc %3 0:i1
%4:i1 = slt 18446744073709551615:i64, %2
%5:i64 = shl %2, 1:i64
%6:i64 = select %4, %5, 18446744073709551615:i64 (hasExternalUses)
%7:i1 = ult %6, 209622091746699451:i64
infer %7
%8:i1 = ult %2, 104811045873349726:i64
result %8

%0:i32 = var
%1:i1 = eq 2139095040:i32, %0
%2:i1 = ne 4286578688:i32, %0
%3:i1 = select %1, 0:i1, %2
infer %3
%4:i1 = xor %1, %2
result %4

Do not include any extra text or markdown formatting. Only produce the output in the prescribed syntax.
"""
}]

def splitOpt(opt):
  lines = opt.split("\n")
  lhs = ""
  rhs = ""
  appendingToLHS = True
  for line in lines:
    if appendingToLHS:
      lhs += line + "\n"
    else:
      rhs += line + "\n"
    # Switch to RHS when we hit the infer line (ignore leading spaces)
    if line.lstrip().startswith("infer"):
      appendingToLHS = False
  return lhs.strip(), rhs.strip()

def add_result_line_if_not_present(rhs):
  """
  Add a 'result %a' line if not present, where %a is the last binding in the RHS.
  """
  import re
  
  lines = rhs.strip().split('\n')
  
  # Check if result line already exists
  for line in lines:
    if line.strip().startswith('result'):
      return rhs  # Already has result line
  
  # Find the last variable binding
  last_var = None
  for line in lines:
    line = line.strip()
    if '=' in line and not line.startswith(';') and not line.startswith('//'):
      # Match patterns like "%z:i32 = " or "%z = "
      match = re.match(r'(%\w+)(?::\w+)?\s*=', line)
      if match:
        last_var = match.group(1)
  
  # Add result line if we found a last variable
  if last_var:
    added = rhs + '\nresult ' + last_var
    logger.debug("added missing result line using last_var=%s", last_var)
    return added
  else:
    return rhs  # No variables found, return as is

def alpha_renaming(lhs, rhs):
  """
  Rename variables in RHS that conflict with variables already defined in LHS.
  This prevents redefinition errors in Souper IR.
  """
  import re
  
  # Extract all variable names defined in LHS (left side of assignments)
  lhs_vars = set()
  for line in lhs.split('\n'):
    line = line.strip()
    if '=' in line and not line.startswith(';') and not line.startswith('//') and not line.startswith('infer') and not line.startswith('result'):
      # Match patterns like "%0:i32 = ", "%var:i8 = ", "%z = ", etc.
      match = re.match(r'(%\w+)(?::\w+)?\s*=', line)
      if match:
        lhs_vars.add(match.group(1))
  
  # Extract all variable definitions in RHS that need renaming
  rhs_lines = rhs.split('\n')
  renamed_rhs_lines = []
  rename_map = {}
  next_var_num = 0
  
  # Find the highest numbered variable in LHS to avoid conflicts
  max_var_num = -1
  for var in lhs_vars:
    if var.startswith('%') and var[1:].isdigit():
      max_var_num = max(max_var_num, int(var[1:]))
  
  next_var_num = max_var_num + 1
  
  rename_count = 0
  for line in rhs_lines:
    line = line.strip()
    if not line:
      renamed_rhs_lines.append(line)
      continue
      
    # Check if this line defines a variable that conflicts with LHS
    if '=' in line and not line.startswith(';') and not line.startswith('//') and not line.startswith('result'):
      # Match patterns like "%z:i32 = " or "%z = "
      match = re.match(r'(%\w+)(?::\w+)?\s*=', line)
      if match:
        var_name = match.group(1)
        if var_name in lhs_vars:
          # Need to rename this variable
          if var_name not in rename_map:
            new_var_name = f"%{next_var_num}"
            rename_map[var_name] = new_var_name
            next_var_num += 1
            rename_count += 1
          
          # Replace the variable definition - handle both typed and untyped variables
          if ':' in line.split('=')[0]:
            # Typed variable like "%z:i32 = "
            line = re.sub(r'%' + re.escape(var_name[1:]) + r'(?=:)', rename_map[var_name], line)
          else:
            # Untyped variable like "%z = "
            line = line.replace(var_name + ' =', rename_map[var_name] + ' =', 1)
    
    # Apply any existing renamings to variable uses in this line
    for old_var, new_var in rename_map.items():
      # Replace variable uses (but be careful not to replace parts of other variables)
      # Use word boundaries to ensure we only replace complete variable names
      line = re.sub(r'\b' + re.escape(old_var) + r'\b', new_var, line)
    
    renamed_rhs_lines.append(line)
  
  if rename_count:
    logger.debug("alpha_renaming applied; count=%d map=%s", rename_count, rename_map)
  return '\n'.join(renamed_rhs_lines)

def fixit(lhs, rhs):
  opt = lhs + "\n" + rhs
  with tempfile.NamedTemporaryFile(mode='w', suffix='.opt', prefix='souper_fixit_', delete=False) as f:
    f.write(opt)
    filename = f.name
  
  try:
    result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename, '-fixit'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=S_CHECK_TIMEOUT_SECONDS)
    fixed = result.stdout.strip()
  except subprocess.TimeoutExpired:
    fixed = ""
  finally:
    os.remove(filename)
  
  return fixed

def verify(lhs, rhs):
  # concatenate lhs and rhs
  opt = lhs + "\n" + rhs
  with tempfile.NamedTemporaryFile(mode='w', suffix='.opt', prefix='souper_verify_', delete=False) as f:
    f.write(opt)
    filename = f.name
  
  try:
    # Execute the souper-check binary with the concatenated string
    # and return the stdout of the command
    result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename, '-souper-use-alive'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=S_CHECK_TIMEOUT_SECONDS)
  except subprocess.TimeoutExpired as e:
    result = SimpleNamespace(returncode=1, stdout="", stderr="verification timeout")
    logger.warning("souper-check verification timeout")
  finally:
    os.remove(filename)
  
  return result

def profit(lhs, rhs, archs=None):
  if archs is None:
    archs = DEFAULT_ARCHITECTURES
    
  opt = lhs + "\n" + rhs
  with tempfile.NamedTemporaryFile(mode='w', suffix='.opt', prefix='souper_ptx_profit_', delete=False) as f:
    f.write(opt)
    filename = f.name

  try:
    # Pre-compute LLVM IR for efficiency (used by multiple modes)
    llvm_rhs_ir_raw = None
    llvm_lhs_ir_raw = None
    llvm_lhs_ir = None
    llvm_rhs_ir = None
    
    # Check if we need LLVM IR for any mode
    needs_llvm = any(arch in ["llvmir"] or arch not in ["souperir"] for arch in archs)
    
    if needs_llvm:
      try:
        llvm_rhs = subprocess.run(['@CMAKE_BINARY_DIR@/souper2llvm', filename, '-rhs'], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
        llvm_rhs_ir_raw = llvm_rhs.stdout.strip()
      except subprocess.TimeoutExpired:
        llvm_rhs_ir_raw = None
        logger.warning("souper2llvm -rhs timeout; skipping llvm profit for this candidate")
      
      try:
        llvm_lhs = subprocess.run(['@CMAKE_BINARY_DIR@/souper2llvm', filename, '-lhs'], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
        llvm_lhs_ir_raw = llvm_lhs.stdout.strip()
      except subprocess.TimeoutExpired:
        llvm_lhs_ir_raw = None
        logger.warning("souper2llvm -lhs timeout; skipping llvm profit for this candidate")

      # Pass through opt -passes=instcombine to apply LLVM optimizations
      opt_bin = "@CMAKE_BINARY_DIR@/../third_party/llvm-Release-install/bin/opt"
      
      try:
        opt_lhs = subprocess.run([opt_bin, '-S', '-O3'], input=llvm_lhs_ir_raw, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
        llvm_lhs_ir = opt_lhs.stdout.strip()
      except subprocess.TimeoutExpired:
        llvm_lhs_ir = None
        logger.warning("opt O3 lhs timeout")
      
      try:
        opt_rhs = subprocess.run([opt_bin, '-S', '-O3'], input=llvm_rhs_ir_raw, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
        llvm_rhs_ir = opt_rhs.stdout.strip()
      except subprocess.TimeoutExpired:
        llvm_rhs_ir = None
        logger.warning("opt O3 rhs timeout")

    profits = []
    for arch in archs:
      if arch == "souperir":
        # Use souper-check -print-profit
        try:
          result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename, '-print-profit'], 
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=S_CHECK_TIMEOUT_SECONDS)
          profit_value = int(result.stdout.strip()) if result.stdout.strip() else 0
          profits.append(profit_value)
        except (ValueError, subprocess.SubprocessError, subprocess.TimeoutExpired):
          profits.append(0)
      elif arch == "llvmir":
        # Count LLVM IR lines
        try:
          lhs_lines = len([line for line in llvm_lhs_ir.split('\n') if line.strip() and not line.strip().startswith(';')])
          rhs_lines = len([line for line in llvm_rhs_ir.split('\n') if line.strip() and not line.strip().startswith(';')])
          profits.append(lhs_lines - rhs_lines)
        except:
          profits.append(0)
      else:
        # Regular architecture - use llc
        try:
          llc_bin = "@CMAKE_BINARY_DIR@/../third_party/llvm-Release-install/bin/llc"
          llc_common = [llc_bin, '-march=' + arch]
          if arch == 'riscv64':
            llc_common = llc_common + ['-mattr=+c,+m,+b,+f,+d,+q,+zfh']
          ptx_lhs = subprocess.run(llc_common, input=llvm_lhs_ir, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
          ptx_rhs = subprocess.run(llc_common, input=llvm_rhs_ir, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)

          ptx_lhs_output = ptx_lhs.stdout.strip()
          ptx_rhs_output = ptx_rhs.stdout.strip()

          # Count non-empty, non-comment lines in assembly output
          lhs_lines = len([line for line in ptx_lhs_output.split('\n') if line.strip() and not line.strip().startswith('//')])
          rhs_lines = len([line for line in ptx_rhs_output.split('\n') if line.strip() and not line.strip().startswith('//')])
          
          profits.append(lhs_lines - rhs_lines)
        except (subprocess.SubprocessError, subprocess.TimeoutExpired):
          profits.append(0)
    
    return profits
  finally:
    os.remove(filename)

def old_profit(lhs, rhs):
  # concatenate lhs and rhs
  opt = lhs + "\n" + rhs
  with tempfile.NamedTemporaryFile(mode='w', suffix='.opt', prefix='souper_profit_', delete=False) as f:
    f.write(opt)
    filename = f.name
  
  try:
    # Execute the souper-check binary with the concatenated string
    # and return the stdout of the command
    result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename, '-print-profit'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=S_CHECK_TIMEOUT_SECONDS)
    return int(result.stdout.strip())
  finally:
    os.remove(filename)

def sort_results(results):
  return sorted(results, key=lambda x: max(x['profits']) if isinstance(x['profits'], list) else x['profits'], reverse=True)

def process_response(lhs, response, min_profit, archs=None, debug_level=0):
  if archs is None:
    archs = DEFAULT_ARCHITECTURES
  result = dict()
  result['valid'] = list()
  result['invalid'] = list()
  result['fixit_count'] = 0
  for choice in response.choices:
    rhs = choice.message.content if getattr(choice, 'message', None) else None
    # Skip empty/whitespace-only outputs from the model; add a guidance message instead
    if not rhs or not str(rhs).strip():
      result['invalid'].append({
        "role": "user",
        "content": "Empty output. Please produce only the RHS lines for the optimization, ending with a result line.",
      })
      if debug_level >= 1:
        logger.info("Skipping empty completion from model")
      continue
    # Normalize to string
    rhs = str(rhs)
    # Add result line if not present
    rhs = add_result_line_if_not_present(rhs)
    # Apply alpha renaming to avoid variable redefinition conflicts
    rhs = alpha_renaming(lhs, rhs)
    
    # Check if RHS introduces a new path condition
    if "pc " in rhs:
      result['invalid'].append({
        "role": "assistant",
        "content": rhs,
      })
      result['invalid'].append({
        "role": "user",
        "content": "RHS can not have a new path condition.",
      })
      continue
    
    oracle = verify(lhs, rhs)
    # print(rhs)
    if oracle.returncode == 0 and "LGTM" in oracle.stdout:
      # result['valid'].append(rhs)
      profits = profit(lhs, rhs, archs=archs)
      if any(p >= min_profit for p in profits):
        if debug_level >= 1:
          logger.info("Accepted candidate; profits=%s", profits)
          logger.info("Accepted RHS:\n%s", rhs)
        result['valid'].append({
          "rhs": rhs,
          "profits": profits,
          "used_fixit": False,
        })
      else:
        if debug_level >= 1:
          logger.info("Rejected by profit; profits=%s min=%d", profits, min_profit)
          logger.info("Rejected RHS (profit):\n%s", rhs)
        result['invalid'].append({
          "role": "assistant",
          "content": rhs,
        })
        profit_str = " ".join(f"{arch} {p}" for arch, p in zip(archs, profits))
        result['invalid'].append({
          "role": "user",
          "content": "Not profitable enough: " + profit_str + " are all less than the "
          "minimum acceptable profit :" + str(min_profit),
        })
    elif (fixed:= fixit(lhs, rhs)) != "":
      result['fixit_count'] += 1
      newlhs, newrhs = splitOpt(fixed)
      used_fixit_flag = True
      if not newrhs or not newrhs.strip():
        if debug_level >= 1:
          logger.info("fixit produced empty RHS; falling back to pre-fixit rhs")
        newlhs, newrhs = lhs, rhs
        used_fixit_flag = False
      profits = profit(newlhs, newrhs, archs=archs)

      if any(p >= min_profit for p in profits):
        if debug_level >= 1:
          logger.info("Accepted candidate (fixit=%s); profits=%s", used_fixit_flag, profits)
          logger.info("Accepted RHS:\n%s", newrhs)
        result['valid'].append({
          "rhs": newrhs,
          "profits": profits,
          "used_fixit": used_fixit_flag,
        })
      else:
        result['invalid'].append({
          "role": "assistant",
          "content": newrhs,
        })
        profit_str = " ".join(f"{arch} {p}" for arch, p in zip(archs, profits))
        result['invalid'].append({
          "role": "user",
          "content": "Not profitable enough: " + profit_str + " are all less than the "
          "minimum acceptable profit :" + str(min_profit),
        })
    else:
      # Only record assistant content if non-empty to avoid API 400 on next turn
      if rhs and rhs.strip():
        result['invalid'].append({
          "role": "assistant",
          "content": rhs,
        })

      if oracle.stderr.strip() != "":
        if debug_level >= 1:
          logger.info("Rejected by verification (stderr):\n%s", oracle.stderr)
          logger.info("Rejected RHS (verify):\n%s", rhs)
        result['invalid'].append({
        "role": "user",
        "content": "Error : " + oracle.stderr,
      })
      elif oracle.stdout.strip() != "":
        if debug_level >= 1:
          logger.info("Rejected by verification (stdout):\n%s", oracle.stdout)
          logger.info("Rejected RHS (verify):\n%s", rhs)
        result['invalid'].append({
        "role": "user",
        "content": "The result is invalid for this input : " + oracle.stdout,
      })
      else :
        result['invalid'].append({
          "role": "user",
          "content": "Error, please try again.",
        })
  return result

def infer(lhs, model, debug=False, max_tries = 4, min_profit = 1, archs=None, debug_level: int = 0):
  if archs is None:
    archs = DEFAULT_ARCHITECTURES
  global log
  log.append({
    "role": "user",
    "content": lhs,
    })

  start_time = time.time()
  overall_timeout = 300.0
  tries = 0
  invalid = set()
  reasoning = "minimal"
  reasoning_models = ["gpt-5-20250807", "qwen-qwen-235b"]
  while True:
    # Overall timeout guard
    if time.time() - start_time > overall_timeout:
      if debug:
        logger.warning("overall inference timeout reached")
      elapsed_time = time.time() - start_time
      return (False, "; Failed to infer RHS tries " + str(tries) + " fixit 0 time {:.2f}s\n".format(elapsed_time))
    # Sanitize messages to ensure no empty contents are sent
    sanitized_log = [m for m in log if isinstance(m, dict) and m.get("content") and str(m["content"]).strip()]
    if debug_level >= 1 and len(sanitized_log) != len(log):
      logger.info("sanitized messages; removed=%d kept=%d", len(log) - len(sanitized_log), len(sanitized_log))
    try:
      if (model in reasoning_models):
        chat_completion = call_openai_with_retry(
          lambda: client.chat.completions.create(
            messages = sanitized_log, model=model, n = 1, reasoning_effort=reasoning),
          request_timeout=30.0, max_retries=2, debug=debug)
      else:
        chat_completion = call_openai_with_retry(
          lambda: client.chat.completions.create(
            messages = sanitized_log, model=model, n = 1),
          request_timeout=30.0, max_retries=2, debug=debug)
    except Exception as e:
      if debug:
        logger.error("openai call failed gracefully; err=%s", e)
      elapsed_time = time.time() - start_time
      # Report a normal failure instead of crashing
      return (False, "; Failed to infer RHS tries " + str(tries) + " fixit 0 time {:.2f}s\n".format(elapsed_time))

    tries += 1
    if debug_level >= 1:
      logger.info("num_tries=%d", tries)

    results = process_response(lhs, chat_completion, min_profit, archs=archs, debug_level=debug_level)

    if results['valid']:
      if debug_level >= 1:
        logger.info("valid_count=%d", len(results['valid']))
      best_result = sort_results(results['valid'])[0]
      elapsed_time = time.time() - start_time
      comment = "; tries " + str(tries)
      comment += " fixit " + ("1" if best_result['used_fixit'] else "0")
      # Format profits as "arch1 p1 arch2 p2 ..."
      profit_str = " ".join(f"{arch} {p}" for arch, p in zip(archs, best_result['profits']))
      comment += " " + profit_str
      comment += " time {:.2f}s".format(elapsed_time)
      return (True, best_result['rhs'] + "\n" + comment + "\n")
    else :
      if debug_level >= 1:
        logger.info("invalid_count=%d", len(results['invalid']))
      log = log + results['invalid']

    # Quit if no new invalid results are generated
    foundNewInvalid = False
    for i in results['invalid']:
      if i['role'] == "assistant":
        if i['content'] not in invalid:
          foundNewInvalid = True
          invalid.add(i['content'])
    if not foundNewInvalid:
      if debug:
        logger.debug("no new invalid results; quitting")
      elapsed_time = time.time() - start_time
      return (False, "; Failed to infer RHS tries " + str(tries) + " fixit 0 time {:.2f}s\n".format(elapsed_time))

    if tries >= max_tries/2:
      log = log[0:2] # clear the log, take a fresh look at the problem

    # if tries >= 1:
    #   model = flip_model(model)
    # if tries >= int(max_tries * 0.7):
    #   model = flip_model(model)

    if tries >= max_tries:
      elapsed_time = time.time() - start_time
      return (False, "; Failed to infer RHS tries " + str(tries) + " fixit 0 time {:.2f}s\n".format(elapsed_time))


# Usable models so far
# claude-sonnet-4-20250514
# gpt-4-turbo
# qwen-qwen-235b
# nvidia-llama-3.1-nemotron-ultra-253b-v1
# gpt-5-20250807
# claude-sonnet-4-5-20250929

if __name__ == "__main__":

  parser = argparse.ArgumentParser(
    prog='souper-infer-openai.py',
    description='souper-check -infer-rhs clone using OpenAI',)

  parser.add_argument('filename', nargs='?')
  parser.add_argument('-d', '-souper-debug-level', default=0, type=int, help='Debug level')
  parser.add_argument('-c', '-souper-external-cache',
                    action='store_true')
  parser.add_argument('-i', '--improve-profit', default=1, help='Try to improve profit')
  parser.add_argument('-m', '--model', help='Model to use', default="claude-sonnet-4-20250514")
  parser.add_argument('-a', '--arch', 
                    help='Comma-separated list of architectures for profit calculation (default: x86-64,aarch64,riscv64,souperir)',
                    default=','.join(DEFAULT_ARCHITECTURES))
  args = parser.parse_args()
  
  # Parse architectures from comma-separated string
  archs = [a.strip() for a in args.arch.split(',') if a.strip()]

  # Configure logging: -d >= 5 => DEBUG, 1..4 => INFO, 0 => WARNING
  if args.d and args.d >= 5:
    logging.basicConfig(level=logging.DEBUG, format='[%(levelname)s] %(message)s')
    # Allow library debug logs when explicitly requested
  elif args.d and args.d >= 1:
    logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
    # Suppress noisy library INFO logs from external libs
    for _name in (
      "httpx",
      "httpcore",
      "openai",
      "azure",
      "azure.core",
      "azure.core.pipeline",
      "azure.core.pipeline.policies",
      "azure.core.pipeline.policies.http_logging_policy",
    ):
      logging.getLogger(_name).setLevel(logging.WARNING)
  else:
    logging.basicConfig(level=logging.WARNING, format='[%(levelname)s] %(message)s')
    # Suppress noisy library INFO logs unless debug is enabled
    for _name in (
      "httpx",
      "httpcore",
      "openai",
      "azure",
      "azure.core",
      "azure.core.pipeline",
      "azure.core.pipeline.policies",
      "azure.core.pipeline.policies.http_logging_policy",
    ):
      logging.getLogger(_name).setLevel(logging.WARNING)

  lhs = ""
  if args.filename:
    lhs = open(args.filename, "r").read()
  else:
    lhs = sys.stdin.read()

  if not args.c:
    success, rhs = infer(lhs, args.model, args.d >= 5, archs=archs, debug_level=args.d)
    print(rhs)
  else:
    r = redis.Redis(host='localhost', port=6379, decode_responses=True)
    if rhs := r.hget(lhs, "rhs"):
      print(lhs, rhs)
    else :
      success, rhs = infer(lhs, args.model, args.d >= 5, min_profit=1, archs=archs, debug_level=args.d)
      if not success:
        r.hset(lhs, "noinfer", "noinfer")
      else :
        success2, rhs2 = infer(lhs, args.model, args.d >= 5, min_profit=2, archs=archs, debug_level=args.d)
        if not success2:
          # Only store RHS if it contains meaningful content (non-empty and has non-whitespace)
          if rhs and rhs.strip():
            r.hset(lhs, "rhs", rhs)
          else:
            r.hset(lhs, "noinfer", "noinfer")
        else:
          # Only store RHS2 if it contains meaningful content
          if rhs2 and rhs2.strip():
            r.hset(lhs, "rhs", rhs2)
            print(rhs2)
          else:
            # Fall back to rhs if rhs2 is empty but rhs has content
            if rhs and rhs.strip():
              r.hset(lhs, "rhs", rhs)
            else:
              r.hset(lhs, "noinfer", "noinfer")
      print(rhs)
