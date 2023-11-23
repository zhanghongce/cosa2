import os
import subprocess
from multiprocessing import Pool
import argparse
import logging 
from functools import partial
import pandas as pd

parser = argparse.ArgumentParser()

parser.add_argument('test_case', action='store', type=str)
parser.add_argument('result_folder', action='store', type=str)
# parser.add_argument('excel_file', action='store', type=str)
# parser.add_argument('logging_failure', action='store', type=str)

args=parser.parse_args()


# df = pd.read_excel(args.excel_file)

# btor_filenames = df['BTOR Filename'].tolist()
# btor_sat_unsat = df['BTOR SAT/UNSAT'].tolist()


if not os.path.exists(args.result_folder):
    os.makedirs(args.result_folder)
logging_failure = os.path.join(args.result_folder,"logging_failure.txt")
logging_coi = os.path.join(args.result_folder,"summary_coi.txt")
logging_pivot_input = os.path.join(args.result_folder,"summary_pivot.txt")

file_list = []
root_directory = os.getcwd() 
# abs_path = os.path.join(root_directory,args.test_case)
# file_list.append(abs_path) 
for root, _, files in os.walk(args.test_case):
    for file in files:
        if file.endswith(".btor") or file.endswith(".btor2"):  
            file_path = os.path.join(root, file)
            abs_path = os.path.join(root_directory,file_path)
            # filename = os.path.relpath(file_path, os.getcwd() )
            # if filename in skip_files:
            #     continue
            # file_list.append(file_path)
            
            # if file_path in btor_filenames:
            #     index = btor_filenames.index(file_path)
                # if btor_sat_unsat[index] == "unknown":
                #     # print(f"Skipping {filename} because SAT/UNSAT is unknown.")
                #     continue
            file_list.append(abs_path) 

def run_with_timeout(btor_path, timeout,logging_coi, logging_pivot_input):
    command_to_run = ["pono", "--bound","500","--logging-smt-solver",
                # "--vcd",
                # "cex.vcd",
                "--promote-inputvars",
                "--dynamic_coi_up_cex",
                "--coi_check",
                "--pivot_input",
                "-e", "bmc",
                "--logging_coi", logging_coi,
                "--logging_pivot_input", logging_pivot_input,
                btor_path]
    process = subprocess.Popen(command_to_run, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate()
        raise TimeoutError("{} | running time out in {} s.".format(btor_path, timeout))
    return stdout.decode(), stderr.decode()

def write_hwmcc_out(filename,log, logging_coi, logging_pivot_input):
     logging.basicConfig(filename=log, level=logging.INFO,
                        format="%(asctime)s - %(levelname)s - %(message)s")

     try:
        stdout, stderr = run_with_timeout(filename, 3600,logging_coi, logging_pivot_input)
        print(stdout)
        if "unknown" in stdout:
            logging.info("{} is Unknown".format(filename))
        elif "sat" in stdout:
            logging.info("{} is SAT".format(filename))
        if stderr:
            logging.error("{}".format(stderr))
     except Exception as e:
         logging.error(str(e))

def ex_pono(file_path,logging_failure, logging_coi, logging_pivot_input):
    relative_path = os.path.basename(file_path)
    result_subfolder = os.path.join(args.result_folder, relative_path)
    os.makedirs(result_subfolder, exist_ok=True)

    
    current_directory = os.getcwd()  
    os.chdir(result_subfolder)  
    logging_failure = os.path.join(current_directory,logging_failure)
    logging_coi = os.path.join(current_directory,logging_coi)
    logging_pivot_input = os.path.join(current_directory,logging_pivot_input)
    
    write_hwmcc_out(file_path,logging_failure,logging_coi, logging_pivot_input)
    
    os.chdir(current_directory)


if __name__ == "__main__":
    pool = Pool(processes=1)  
    ex_pono_partisal = partial(ex_pono, logging_failure=logging_failure, logging_coi=logging_coi, logging_pivot_input=logging_pivot_input)
    pool.map(ex_pono_partisal, file_list)
    pool.close()
    pool.join()


