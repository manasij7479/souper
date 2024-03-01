import sys
import os
import subprocess
import argparse
import redis
from openai import OpenAI

client = OpenAI(
  api_key=os.environ.get("OPENAI_API_KEY"),
)

max_tries = 5

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
Name of variables and expressions are prefixed with %.
A pc is a boolean precondition that implies a valid optimization.
The syntax is: pc %0 1, means that the optimization is valid when %%0 is 1.
The operations available are: add, sub, mul, udiv, sdiv, urem, srem, and, or, xor, shl, lshr, ashr, eq, ne, ugt, uge, ult, ule, sgt, sge, slt, sle.
Do not explain the optimizations, just generate the replacement.
Do not regenerate the existing infer command.
Do not start a line with a variable that has already been defined.
Do not declare new variables.
Do not generate more operations than necessary.
Try to generate the simplest replacement possible.
Try to come up with new constants by cleverly combining existing ones.
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
"""
}]

def verify(lhs, rhs):
  # concatenate lhs and rhs
  opt = lhs + "\n" + rhs
  # write the concatenated string to a file
  with open("/tmp/out.opt", "w") as f:
    f.write(opt)
  # Execute the souper-check binary with the concatenated string
  # and return the stdout of the command

  result = subprocess.run(['./souper-check', '/tmp/out.opt'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  return result

def profit(lhs, rhs):
  # concatenate lhs and rhs
  opt = lhs + "\n" + rhs
  # write the concatenated string to a file
  with open("/tmp/out.opt", "w") as f:
    f.write(opt)
  # Execute the souper-check binary with the concatenated string
  # and return the stdout of the command

  result = subprocess.run(['./souper-check', '/tmp/out.opt', '-print-profit'] , stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  return int(result.stdout.strip())

# Needs to be more sophisticated?
def flip_model(m):
  if m == "gpt-4":
    return "gpt-3.5-turbo"
  elif m == "gpt-3.5-turbo":
    return "gpt-4"
  else:
    return "gpt-3.5-turbo"

def sort_results(results):
  return sorted(results, key=lambda x: x['profit'], reverse=True)

def process_response(lhs, response):
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
      if p >= 0:
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
          "content": "Not profitable enough: " + str(p),
        })
    else:
      result['invalid'].append({
        "role": "assistant",
        "content": rhs,
      })
      result['invalid'].append({
        "role": "user",
        "content": "Error : " + oracle.stderr + oracle.stdout,
      })
  return result

def infer(lhs, debug=False):
  global log
  log.append({
    "role": "user",
    "content": lhs,
    })

  # model = "gpt-4-1106-preview"
  # model = "gpt-4-0125-preview"
  model = "gpt-4-turbo-preview"
  # model = "gpt-3.5-turbo"
  # model = "gpt-4"
  # model = "null"

  oracle = "init"
  tries = 0
  while True:
    chat_completion = client.chat.completions.create(
      messages = log, model=model, n = 4, temperature=0.7, presence_penalty=0.5, frequency_penalty=0.5)
    # TODO : Try tweaking these parameters
    tries += 1
    if debug:
      print("Num tries: ", tries)

    results = process_response(lhs, chat_completion)

    if results['valid']:
      if debug:
        print ("Valid results: ", results['valid'])
      return sort_results(results['valid'])[0]['rhs']
    else :
      if debug:
        print("Invalid results: ", results['invalid'])
      log = log + results['invalid']

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
      rhs = infer(lhs, int(args.d) > 0)
      if rhs == "Failed to infer RHS.":
        r.hset(lhs, "noinfer", "noinfer")
      else :
        r.hset(lhs, "rhs", rhs)
      print(rhs)


