import subprocess
import os
import argparse
import datetime
from loguru import logger
def try_rm(name):
    try:
        os.remove(name)
    except:
        pass

def try_open(inv_file):
     try:
          count_file = len(open(inv_file,'r').readlines())
     except:
          count_file = 0
     return count_file

if __name__ == '__main__':
     parser = argparse.ArgumentParser()
     parser.add_argument('--path_cex', type=str,default='cex.vcd')
     parser.add_argument('--engine', type=str,default='sygus-pdr')
     # parser.add_argument('--ILA_path', type=str,default='/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/verify_two/ADD/')
     parser.add_argument('--path_design', type=str,default='/data/zhiyuany/EnvSynSamples/ILAng/AES/envinvsyn/design.btor')
     parser.add_argument('--ILA_model', type=str,default='/data/zhiyuany/EnvSynSamples/ILAng/AES/verification/LOAD/problem.btor2')
     parser.add_argument('--inv_path', type=str,default='inductive_invariant')
     parser.add_argument('--init-term-width', type=int, default=4, metavar='N',
                    help='Initial terms width')
     parser.add_argument('--continue_from',action='store_true',default=False,
                    help='Select the model is to detect solution, or the satisfiable')
     parser.add_argument('--continue-file', type=str,default=None)
     parser.add_argument('--log-dir', type=str, default='log', help='log folder dir')
     opts = parser.parse_args(args=[
          '--path_cex','cex_2.vcd',
          '--engine','sygus-pdr',
          '--path_design','/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/output/design.btor',
          '--ILA_model' , '/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/verify_two/ADD/problem.btor2',
          '--inv_path','inductive_invariant'
          # '--continue_from',
          # '--continue-file','inv.smt2'
          ])
     exp_name = 'initial_term_width:{:d}_engine:{}_design{}'.format(opts.init_term_width,opts.engine,opts.path_design)
     log_dir = os.path.join(opts.log_dir,exp_name + '.log')
     logger.add(log_dir)
     logger.info(opts)
     cosa_path = os.getcwd()
     path_cex  = opts.path_cex
     engine = opts.engine
     init_term_width = opts.init_term_width
     path_design = opts.path_design
     count = 0 
     count_file = 0
     inv_path = os.path.join(cosa_path,opts.inv_path)
     
     starttime = datetime.datetime.now()
     if(os.path.exists(inv_path) == False):
          os.mkdir(inv_path)
     if opts.continue_from == False:
          while(count == count_file):
               inv_file = os.path.join(inv_path,'inv' +'.smt2')
               inv_origin = os.path.join(inv_path,'inv_origin.smt2')
               if count ==0:
                    try_rm(path_cex)
                    try_rm(inv_file)
                    try_rm(inv_origin)
                    subprocess.run(["./build/pono","--vcd", "{:s}" .format(path_cex),"-e","{:s}" .format("ind"), "{:s}" .format(opts.ILA_model)])
                    if os.path.exists(path_cex) == False:
                         # print("The enviroment invariant is found")
                         logger.info("The enviroment invariant is found")
                         break
                    logger.info("The step is {:d}" .format(count))
                    # print("The step is {:d}" .format(count))
                    subprocess.run(["./build/pono-env","--engine","{:s}" .format(engine),"--bound","{:s}" .format("10"),"--cex-reader","{:s}" .format(path_cex),
                    "--num-of-itr","{:s}" .format(str(count)),"--sygus-initial-term-width","{:s}" .format(str(init_term_width)),
                    "--find-environment-invariant","--show-invar","--promote-inputvars","--smtlib-path","{:s}" .format(inv_path),"{:s}" .format(path_design)])
                    count = count +1
                    count_file = try_open(inv_file)
                    # count_file = len(open(inv_file,'r').readlines())
                    if count !=count_file:
                         # print("The enviroment invariant can not be found, the design is unsafe")
                         logger.info("The enviroment invariant can not be found, the design is unsafe")
                         break
                    logger.info("The original bad state is blocked, continue to the next step")
               else:
                    # os.chdir(opts.ILA_path)
                    # path = os.getcwd()
                    try_rm(path_cex)
                    subprocess.run(["./build/pono","--vcd" , "{:s}" .format(path_cex),"-e","{:s}" .format("ind"), "--property-file", "{:s}" .format(inv_file),"{:s}" .format(opts.ILA_model)])
                    if os.path.exists(path_cex) == False:
                         logger.info("The enviroment invariant is found")
                         break
                    logger.info("The step is {:d}" .format(count))
                    # print("The step is {:d}" .format(count))           
                    subprocess.run(["./build/pono-env","-e","{:s}" .format(engine),"--bound","{:s}" .format("10"),"--cex-reader","{:s}" .format(path_cex),
                    "--num-of-itr","{:s}" .format(str(count)),"--sygus-initial-term-width","{:s}" .format(str(init_term_width)),
                    "--find-environment-invariant","--show-invar","--promote-inputvars","--smtlib-path","{:s}" .format(inv_path),"{:s}" .format(path_design)])
                    count_file = try_open(inv_file)
                    # count_file = len(open(inv_file,'r').readlines()) 
                    count = count+1     
                    if count !=count_file:
                         logger.info("The enviroment invariant can not be found, the design is unsafe")
                         break       
                    logger.info("The original bad state is blocked, continue to the next step")
     else:
          assert(opts.continue_file is not None)
          inv_file = opts.continue_file
          inv_file = os.path.join(inv_path,inv_file)
          count = len(open(inv_file,'r').readlines(opts.continue_file))
          logger.info('Continue training from {}..., the step is{:d}....'.format(opts.continue_file,count))
          count_file = count
          while(count == count_file):
               # os.chdir(opts.ILA_path)
               # path = os.getcwd()
               try_rm(path_cex)
               subprocess.run(["./build/pono","--vcd","{:s}".format(path_cex),"-e","{:s}" .format("ind"), "--property-file", "{:s}" .format(inv_file),"{:s}" .format(opts.ILA_model)])
               if os.path.exists(path_cex) == False:
                    # print("The enviroment invariant is found")
                    logger.info("The enviroment invariant is found")
                    break
               # os.chdir(cosa_path)
               # inv_file = os.path.join(inv_path,'inv' + str(count) +'.smt2')
               # cex_file_cosa = os.path.join(path,path_cex)
               # print("The step is {:d}" .format(count))           
               logger.info("The step is {:d}" .format(count))
               subprocess.run(["./build/pono-env","-e","{:s}" .format(engine),"--bound","{:s}" .format("50"),"--cex-reader","{:s}" .format(path_cex),
               "--num-of-itr","{:s}" .format(str(count)),"--sygus-initial-term-width","{:s}" .format(str(init_term_width)),
               "--find-environment-invariant","--show-invar","--check-invar","--promote-inputvars","--smtlib-path","{:s}" .format(inv_path),"{:s}" .format(path_design)])
               count_file = try_open(inv_file)
               # count_file = len(open(inv_file,'r').readlines())
               count = count+1 
               if count_file !=count:
                    # print("The enviroment invariant can not be found, the design is unsafe")
                    logger.info("The enviroment invariant can not be found, the design is unsafe")
                    break
               logger.info("The original bad state is blocked, continue to the next step")
     endtime = datetime.datetime.now()
     print("The overall running time is {:.4f}" .format((endtime - starttime).seconds))
     logger.info("The overall running time is {:.4f}" .format((endtime - starttime).seconds))
     