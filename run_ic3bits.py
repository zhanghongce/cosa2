import os
import subprocess
from multiprocessing import Pool
import argparse
import time

parser = argparse.ArgumentParser()

parser.add_argument('test_case', action='store', type=str)
# parser.add_argument('result_folder', action='store', type=str)
# parser.add_argument('excel_file', action='store', type=str)
# parser.add_argument('logging_failure', action='store', type=str)

args=parser.parse_args()

command_to_run = ["pono", "--bound","500",
                  "--check-invar",
                "-e", "ic3bits",
                args.test_case]
print(" Running on Enhanced ic3bits\n")
process = subprocess.Popen(command_to_run, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
try:
    t_begin = time.time()
    stdout, stderr = process.communicate(timeout=3600)
    t_end = time.time()
    print(stdout.decode())
    # if('unsat' in stdout):
    #     print('unsat\n')
    # elif('sat' in stdout):
    #     print('sat\n')
    # elif('unknown' in stdout):
    #     print('unknown\n')
    print("The total time on Enhanced ic3bits is: %0.4f"%( t_end-t_begin))
except subprocess.TimeoutExpired:
    process.kill()
    stdout, stderr = process.communicate()
    raise TimeoutError("Enhanced ic3bits | {} | running time out in {} s.".format(args.test_case, 3600))

command_to_run = ["pono", "--bound","500",
                "--check-invar",
                "--ic3bits-no-enhanced-coi",
                "-e", "ic3bits",
                args.test_case]
print(" Running on Vanilla ic3bits\n")
process = subprocess.Popen(command_to_run, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
try:
    t_begin = time.time()
    stdout, stderr = process.communicate(timeout=3600)
    t_end = time.time()
    print(stdout.decode())
    # if('unsat' in stdout):
    #     print('unsat\n')
    # elif('sat' in stdout):
    #     print('sat\n')
    # elif('unknown' in stdout):
    #     print('unknown\n')
    print("The total time on Vanilla ic3bits is: %0.4f"%( t_end-t_begin))
except subprocess.TimeoutExpired:
    process.kill()
    stdout, stderr = process.communicate()
    raise TimeoutError("Vanilla ic3bits | {} | running time out in {} s.".format(args.test_case, 3600))