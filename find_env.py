import subprocess
import os
import argparse
if __name__ == '__main__':
     parser = argparse.ArgumentParser()
     parser.add_argument('--path_cex', type=str,default='cex.vcd')
     parser.add_argument('--engine', type=str,default='sygus-pdr')
     parser.add_argument('--ILA_path', type=str,default='/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/verify_two/ADD/')
     parser.add_argument('--path_design', type=str,default='/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/output/design.btor')
     parser.add_argument('--inv_path', type=str,default='inductive_invariant')
     parser.add_argument('--init-term-width', type=int, default=4, metavar='N',
                    help='Initial terms width')
     parser.add_argument('--continue_from',action='store_true',default=False,
                    help='Select the model is to detect solution, or the satisfiable')
     parser.add_argument('--continue-file', type=str,default=None)
     opts = parser.parse_args(args=[
          '--path_cex','cex_2.vcd',
          '--engine','sygus-pdr',
          '--ILA_path','/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/verify_two/ADD/',
          '--path_design','/data/zhiyuany/ILA-Tools/test/unit-data/vpipe/output/design.btor',
          '--inv_path','inductive_invariant'
          # '--continue_from',
          # '--continue-file','inv.smt2'
          ])
     cosa_path = os.getcwd()
     path_cex  = opts.path_cex
     engine = opts.engine
     init_term_width = opts.init_term_width
     path_design = opts.path_design
     count = 0 
     count_file = 0
     inv_path = os.path.join(cosa_path,opts.inv_path)
     if(os.path.exists(inv_path) == False):
          os.mkdir(inv_path)
     if opts.continue_from == False:
          while(count == count_file):
               inv_file = os.path.join(inv_path,'inv' +'.smt2')
               if count ==0:
                    os.chdir(opts.ILA_path)
                    path = os.getcwd()
                    subprocess.run(["bash run_first.sh"],shell=True)
                    if os.path.exists(path_cex) == False:
                         print("The enviroment invariant is found")
                         break
                    os.chdir(cosa_path)
                    cex_file_cosa = os.path.join(path,path_cex)
                    subprocess.run(["./build/pono-env","-e","{:s}" .format(engine),"--cex-reader","{:s}" .format(cex_file_cosa),
                    "--num-of-itr","{:s}" .format(str(count)),"--sygus-initial-term-width","{:s}" .format(str(init_term_width)),
                    "--find-environment-invariant","--show-invar","--check-invar","--promote-inputvars","--smtlib-path","{:s}" .format(inv_path),"{:s}" .format(path_design)])
                    count = count +1
                    count_file = len(open(inv_file,'r').readlines())
                    if count !=count_file:
                         break
               else:
                    # inv_file_pre = os.path.join(inv_path,'inv' + str(count-1) +'.smt2')
                    os.chdir(opts.ILA_path)
                    path = os.getcwd()
                    subprocess.run(["bash","run.sh","{:s}" .format(path_cex), "{:s}" .format(inv_file)])
                    if os.path.exists(path_cex) == False:
                         print("The enviroment invariant is found")
                         break
                    os.chdir(cosa_path)
                    # inv_file = os.path.join(inv_path,'inv' + str(count) +'.smt2')
                    cex_file_cosa = os.path.join(path,path_cex)           
                    subprocess.run(["./build/pono-env","-e","{:s}" .format(engine),"--cex-reader","{:s}" .format(cex_file_cosa),
                    "--num-of-itr","{:s}" .format(str(count)),"--sygus-initial-term-width","{:s}" .format(str(init_term_width)),
                    "--find-environment-invariant","--show-invar","--check-invar","--promote-inputvars","--smtlib-path","{:s}" .format(inv_path),"{:s}" .format(path_design)])
                    count_file = len(open(inv_file,'r').readlines())
                    count = count+1     
                    if count !=count_file:
                         print("The enviroment invariant can not be found, the design is unsafe")
                         break       
     else:
          assert(opts.continue_file is not None)
          inv_file = opts.continue_file
          inv_file = os.path.join(inv_path,inv_file)
          count = len(open(inv_file,'r').readlines())
          count_file = count
          while(count == count_file):
               # inv_file_pre = os.path.join(inv_path,'inv' + str(count-1) +'.smt2')
               os.chdir(opts.ILA_path)
               path = os.getcwd()
               subprocess.run(["bash","run.sh","{:s}" .format(path_cex), "{:s}" .format(inv_file)])
               if os.path.exists(path_cex) == False:
                    print("The enviroment invariant is found")
                    break
               os.chdir(cosa_path)
               # inv_file = os.path.join(inv_path,'inv' + str(count) +'.smt2')
               cex_file_cosa = os.path.join(path,path_cex)           
               subprocess.run(["./build/pono-env","-e","{:s}" .format(engine),"--cex-reader","{:s}" .format(cex_file_cosa),
               "--num-of-itr","{:s}" .format(str(count)),"--sygus-initial-term-width","{:s}" .format(str(init_term_width)),
               "--find-environment-invariant","--show-invar","--check-invar","--promote-inputvars","--smtlib-path","{:s}" .format(inv_path),"{:s}" .format(path_design)])
               count_file = len(open(inv_file,'r').readlines())
               count = count+1 
               if count_file !=count:
                    print("The enviroment invariant can not be found, the design is unsafe")