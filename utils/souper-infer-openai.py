import sys
import os
import subprocess
import argparse
import redis
from openai import OpenAI

client = OpenAI(
  api_key=os.environ.get("OPENAI_API_KEY"),
)

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
    if line.startswith("infer"):
      appendingToLHS = False
  return lhs.strip(), rhs.strip()

def fixit(lhs, rhs):
  opt = lhs + "\n" + rhs
  filename = "/tmp/" + str(hash(opt)) + ".opt"
  with open(filename, "w") as f:
    f.write(opt)
  result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename, '-fixit'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  fixed = result.stdout.strip()
  os.remove(filename)
  return fixed

def verify(lhs, rhs):
  # concatenate lhs and rhs
  opt = lhs + "\n" + rhs
  filename = "/tmp/" + str(hash(opt)) + ".opt"
  # write the concatenated string to a file
  with open(filename, "w") as f:
    f.write(opt)
  # Execute the souper-check binary with the concatenated string
  # and return the stdout of the command

  result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  os.remove(filename)
  return result

def profit(lhs, rhs):
  # concatenate lhs and rhs
  opt = lhs + "\n" + rhs
  filename = "/tmp/" + str(hash(opt)) + ".opt"
  # write the concatenated string to a file
  with open(filename, "w") as f:
    f.write(opt)
  # Execute the souper-check binary with the concatenated string
  # and return the stdout of the command

  result = subprocess.run(['@CMAKE_BINARY_DIR@/souper-check', filename, '-print-profit'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  os.remove(filename)
  return int(result.stdout.strip())

# # Needs to be more sophisticated?
# def flip_model(m):
#   if m == "gpt-4":
#     return "gpt-3.5-turbo"
#   elif m == "gpt-3.5-turbo":
#     return "gpt-4"
#   else:
#     return "gpt-3.5-turbo"

def sort_results(results):
  return sorted(results, key=lambda x: x['profit'], reverse=True)

def process_response(lhs, response, min_profit):
  result = dict()
  result['valid'] = list()
  result['invalid'] = list()
  for choice in response.choices:
    rhs = choice.message.content
    oracle = verify(lhs, rhs)
    # print(rhs)
    if oracle.returncode == 0 and "LGTM" in oracle.stdout:
      # result['valid'].append(rhs)
      p = profit(lhs, rhs)
      if p >= min_profit:
        result['valid'].append({
          "rhs": rhs,
          "profit": p,
        })
      else:
        result['invalid'].append({
          "role": "assistant",
          "content": rhs,
        })
        result['invalid'].append({
          "role": "user",
          "content": "Not profitable enough: profit " + str(p) + " is less than the "
          "minimum acceptable profit :" + str(min_profit),
        })
    elif (fixed:= fixit(lhs, rhs)) != "":
      newlhs, newrhs = splitOpt(fixed)
      p = profit(newlhs, newrhs)

      if p >= min_profit:
        result['valid'].append({
          "rhs": newrhs,
          "profit": p,
        })
      else:
        result['invalid'].append({
          "role": "assistant",
          "content": newrhs,
        })
        result['invalid'].append({
          "role": "user",
          "content": "Not profitable enough: profit " + str(p) + " is less than the "
          "minimum acceptable profit :" + str(min_profit),
        })
    else:
      result['invalid'].append({
        "role": "assistant",
        "content": rhs,
      })

      if oracle.stderr.strip() != "":
        result['invalid'].append({
        "role": "user",
        "content": "Error : " + oracle.stderr,
      })
      elif oracle.stdout.strip() != "":
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

def infer(lhs, debug=False, model="gpt-4-turbo-preview", max_tries = 4, min_profit = 1):
  global log
  log.append({
    "role": "user",
    "content": lhs,
    })

  tries = 0
  invalid = set()
  while True:
    chat_completion = client.chat.completions.create(
      messages = log, model=model, n = 1, temperature=0.7, presence_penalty=0.5, frequency_penalty=0.5)

    tries += 1
    if debug:
      print("Num tries: ", tries)

    results = process_response(lhs, chat_completion, min_profit)

    if results['valid']:
      if debug:
        print ("Valid results: ", results['valid'])
      return sort_results(results['valid'])[0]['rhs'] + "\n" + "; tries " + str(tries) + "\n"
    else :
      if debug:
        print("Invalid results: ", results['invalid'])
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
        print("No new invalid results are generated. Quitting.")
      return "Failed to infer RHS."

    if tries >= max_tries/2:
      log = log[0:2] # clear the log, take a fresh look at the problem

    # if tries >= 1:
    #   model = flip_model(model)
    # if tries >= int(max_tries * 0.7):
    #   model = flip_model(model)

    if tries >= max_tries:
      return "Failed to infer RHS."

if __name__ == "__main__":

  parser = argparse.ArgumentParser(
    prog='souper-infer-openai.py',
    description='souper-check -infer-rhs clone using OpenAI',)

  parser.add_argument('filename', nargs='?')
  parser.add_argument('-d', '-souper-debug-level', default=0, help='Debug level')
  parser.add_argument('-c', '-souper-external-cache',
                    action='store_true')
  args = parser.parse_args()

  lhs = ""
  if args.filename:
    lhs = open(args.filename, "r").read()
  else:
    lhs = sys.stdin.read()


  if not args.c:
    rhs = infer(lhs, int(args.d) > 0)
    print(rhs)
  else:
    r = redis.Redis(host='localhost', port=6379, decode_responses=True)
    if rhs := r.hget(lhs, "rhs"):
      print(lhs, rhs)
    else :
      rhs = infer(lhs, int(args.d) > 0, min_profit=1)
      if rhs == "Failed to infer RHS.":
        r.hset(lhs, "noinfer", "noinfer")
      else :
        rhs2 = infer(lhs, int(args.d) > 0, min_profit=2)
        if rhs2 == "Failed to infer RHS.":
          r.hset(lhs, "rhs", rhs)
        else:
          r.hset(lhs, "rhs", rhs2)
          print(rhs2)
      print(rhs)


