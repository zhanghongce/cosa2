import os 
import subprocess
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('test_case', action='store', type=str)
args=parser.parse_args()

script1 = 's0_btor_add.py'
script2 = 's1_btor_files.py'
script3 = 's2_btor_run.py'


subprocess.run(['python3', script1] + [args.test_case], check=True)
subprocess.run(['python3', script2] + [args.test_case], check=True)
subprocess.run(['python3', script3] + [args.test_case], check=True)