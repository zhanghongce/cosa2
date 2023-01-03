import subprocess
import os
import argparse
import datetime

# 1.cexgen
# 2.cexvalidate

def try_rm(name):
    try:
        os.remove(name)
    except:
        pass

def run_cegar(n_iteration, qedbtor, dutbtor):
    
    # create envinv.smt2 when necessary
    if not os.path.exists("envinv.smt2"):
        with open("envinv.smt2",'w') as fout:
            fout.write('')
    
    errFlag = False
    while not errFlag:
        try_rm("check.result")
        try_rm("cex.vcd")
        print (datetime.datetime.now(), '--> running QED iter #', n_iteration)
        subprocess.run(["./cexgen","--property-file", "envinv.smt2",qedbtor])
        try:
            result = open('check.result')
        except:
            print ('cexgen failed.')
            errFlag = True
            break
        qed_res = result.readline()
        result.close()
        del result
        
        if 'unsat' in qed_res:
            print ('no more cex. CEGAR termindates.')
            break
        if not 'sat' in qed_res:
            print ('cexgen produced unexpected result:', qed_res)
            errFlag = True
            break
        if not os.path.exists("cex.vcd"):
            print ('cexgen didn\'t produce waveform.')
            errFlag = True
            break
        del qed_res
        
        # now the second part
        try_rm("check.result")
        oldsize = os.path.getsize('envinv.smt2')
        print (datetime.datetime.now(), '--> running cex validation iter #', n_iteration)        
        subprocess.run(["./cexvalidate","--num-of-itr", str(n_iteration), dutbtor])
        
        try:
            result = open('result.txt')
        except:
            print ('cexvalidate failed.')
            errFlag = True
            break
        syn_res = result.readline()
        result.close()
        del result
        
        if 'unreachable' not in syn_res:
            print ('cexvalidate produced unexpected result:', syn_res)
            errFlag = True
            break
            
        newsize = os.path.getsize('envinv.smt2')
        if not (newsize > oldsize):
            print ('envinv size is strange!', oldsize,'--->',newsize)
            errFlag = True
            break
        print(datetime.datetime.now(), '--> finish iter #',n_iteration) 
        n_iteration += 1
                   

if __name__ == '__main__':
     parser = argparse.ArgumentParser()
     parser.add_argument('--iter', type=int,default=0)
     parser.add_argument('--qedbtor', type=str,default='ridecore.btor2')
     parser.add_argument('--dutbtor', type=str,default='ridecore-envsyn.btor2')
     
     opts = parser.parse_args()
     run_cegar(opts.iter, opts.qedbtor, opts.dutbtor)
     
     
     
