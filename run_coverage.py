import os 
import subprocess
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('test_case', action='store', type=str)
args=parser.parse_args()

script1 = 'add_uut_comments.py'
script2 = 'add_uut_files.py'
script3 = 'add_result.py'


subprocess.run(['python3', script1] + [args.test_case], check=True)
subprocess.run(['python3', script2] + [args.test_case], check=True)
subprocess.run(['python3', script3] + [args.test_case], check=True)