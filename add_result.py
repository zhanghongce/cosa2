import os,sys
import subprocess
from multiprocessing.pool import Pool
from multiprocessing import Process
from add_uut_files import GETfile
from add_uut_files import GETfile_mod
from btoruut_1 import cmdname
from btoruut_1 import subprocess_run
from btoruut_1 import reduce
import logging 
import argparse
def getPid(gameproc):
    cmd = "ps aux| grep '%s'|grep -v grep " % gameproc
    logging.info(cmd)
    out = subprocess.Popen(cmd,shell=True,stdout=subprocess.PIPE)
    infos = out.stdout.read().splitlines()
    #print(infos)
    if len(infos) >= 1:
        for i in infos:
            pid = i.split()[1]
        return pid
    else:
        return -1

def reducepid(line):
    str_list = list(line)
    del str_list[0 : 2]
    str_list.pop()
    newline = ''.join(str_list)
    return newline

def delpid(cmd):
    pid = getPid(cmd)
    pid = str(pid)
    pid = reducepid(pid)
    delcmd = 'kill -9 '+ pid
    subprocess.run(args=delcmd,shell=True,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,universal_newlines=True,timeout=5,check=False)
    
    
def cmdname(name,path,t):
    i = name.find('-k')
    name = name[:i]
    newname = name + '-k '+ str(t) + ' '+ path
    return newname

def subprocess_run(str_shell):
    try:
        CompletedProcessObject=subprocess.run(args=str_shell,shell=True,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,universal_newlines=True,timeout=3600,check=False)
        if CompletedProcessObject:
            code,out,err=CompletedProcessObject.returncode,CompletedProcessObject.stdout,CompletedProcessObject.stderr
            return out

    except subprocess.TimeoutExpired:
        print('this file timeout')
        delpid(str_shell)
        return 0

def reduce(line):
    print('this is line: ',line)
    str_list = list(line)
    i = line.find('here')
    del str_list[0 : i+4]
    str_list.pop()
    str_list.pop()
    str_list.pop()
    newline = ''.join(str_list)
    return newline
###get one file run this
##filename run by turn,write result
def GETbound(path):
    with open(path,'r')as f:
        while True:
            line = f.readline()
            print(line)
            if 'depth' in line:
                print(line)
                list_line = line.split()
                print(list_line)
                k = int(list_line[-1])
                return k
            
def GETfile_init(root):
    for root, dirs, files in os.walk(root, topdown=False):
        for name in files:
            if(name.find('btor_new.btor') >= 0):# for new folder ,one loop
                path = os.path.join(root, name)
                file_list,linenum,linechange,linenotchange = GETfile(path)
                filespaths = GETfile_mod(file_list,linenum,linechange,name,root)
                return linenotchange,filespaths
            
def GETresult_line():
    parser = argparse.ArgumentParser()
    parser.add_argument('test_case', action='store', type=str)
    args=parser.parse_args()
    list_result = []
    folder = './modbtor'
    if(os.path.exists(folder)==False):
        os.mkdir(folder)
    with open( os.path.join(folder,'final_result') ,'w',encoding='utf-8')as f:
        for root, dirs, files in os.walk(args.test_case, topdown=False):#get btor files
            for name in files:
                if 'config.sby' in name:
                    onefile_result = []
                    f.write(root +'\n')
                    path = os.path.join(root, name)
                    print(path)
                    bound_path = path
                    t = GETbound(path) #get bmc bound
                    str_shell='./build/pono --coverage_alalyze --logging-smt-solver -k ' + str(t) + ' ./crafted/cav14_example/cav14_example.btor2'
                    linenotchange,filespaths = GETfile_init(root) #run files by names, write result,for one paath one file result
                    fileamount = 0
                    coi_covered = 0
                    unknown = 0
                    timeout = 0
                    with open(root +'/'+ 'result' ,'w',encoding='utf-8')as g:
                        line = path + '\n'
                        g.write(line)
                        for filepath in filespaths:
                            i = filespaths.index(filepath)
                            str_shell = cmdname(str_shell,filepath,t)
                            print(str_shell)
                            line = p.apply_async(subprocess_run, args = (str_shell,)).get()
                            line = reduce(line)
                            if i==0 :
                                listline = root + ' ' + 'init file' + line
                                onefile_result.append(listline)
                                g.write('the init file result: ' +'\n')
                                g.write(line+'\n')
                            else:
                                line = linenotchange[i-1] + ' '+ line + '\n'
                                g.write(line)
                                listline = root + '\n'+ line
                                onefile_result.append(listline)
                                fileamount += 1
                                if 'unknown' in line:
                                    unknown += 1
                                if 'is_covered: 1' in line:
                                    coi_covered += 1
                                if 'timeout' in line:
                                    timeout += 1
                    list_result.append(onefile_result)
                    line = 'the fileamount is:'+ str(fileamount)+'\n'
                    f.write(line)
                    line = 'the covered is:'+ str(coi_covered) +'\n'
                    f.write(line)
                    line = 'the unknown is:'+ str(unknown)+'\n'
                    f.write(line)
                    line = 'the timeout is:'+ str(timeout)+'\n'
                    f.write(line)
    return list_result
    
def GETresult(list_result):#get the 65 *n list and write cpnpared result
    k = len(list_result[0])
    for i in range(k):
        with open('./modbtor' +'/'+ str(i) ,'w',encoding='utf-8')as f:
            for vec in list_result:
                line = vec[i]
                f.write(line)

def main():
    list_result = GETresult_line()
    GETresult(list_result)


if __name__=='__main__':
    ###write loop
    p = Pool(1)
    main()
    p.close()
    p.join()