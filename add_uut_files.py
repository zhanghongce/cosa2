#
#get the line num -> run the file -> write the result in filename_result.txt
#how to run files in turn ? ->1. new code run   2. old code 
#new code : read file run it write result
#

import os,sys
import subprocess
import argparse
list_sort = ['sort','input','const']# no index
list_state = ['state','constraint','bad']#only index
list_normal2 = ['not','redor','redand']
list_normal3 = ['init','next','eq','or','add','ult','and','concat','neq','sub','slt','sra','sll','xor','read','ugte','srl','ugt']
list_normal4 = ['ite']
list_test = ['sort','input','const',\
             'state','constraint','bad',\
                'not','redor','redand',\
                    'init','next','eq','or','add','ult','and','concat',\
                        'neq','sub','slt','sra','sll','xor','read','ugte','srl','ugt',\
                            'ite']

list_bitop = ['and','nand','nor','or','xnor','xor']
list_arith = ['add','mul','div','smod','rem','sub']
list_overflow = ['addo','divo','mulo','subo']
list_all = list_bitop + list_arith + list_overflow
list_notap = []

'''def Process(line,linenum,linechange):
    list_line = line.split()
    if '*uut' in list_line:
        list_line.pop()
        if list_line[1] in list_all and len(list_line) >= 2:
            list_line.append('###UF###\n')
            linenum.append(list_line[0])#get the substitude line num
            line = ' '.join(list_line)
            #print('after process:',line)
            linechange.append(line)
    return linenum,linechange
'''
def Filesname(name,t):#new name for btorfiles 
    b = '2_'+ str(t)
    i = name.find('.btor')
    newname = name[:i] + b + '.btor'
    return newname

def GETfile(path):
    file_list = []
    linenum = []
    linechange = []
    linenotchange = []
    with open(path,encoding='utf-8')as f:
        while True:
            line= f.readline()
            list_line = line.split()
            if '*uut' in line:
                pos = line.find('*uut')
                newline = line[:pos] 
                file_list.append(newline+ '\n')
                if list_line[1] in list_all:
                    linenotchange.append(newline)
                    changeline = newline + ' ###UF###\n'
                    linenum.append(int(list_line[0]))#get the substitude line num
                    #print('after process:',line)
                    linechange.append(changeline)
                else:pass
            else:
                file_list.append(line)
            if not line:break
    return file_list,linenum,linechange,linenotchange

def GETfile_mod(file_list,linenum,linechange,name,root):
    filespaths = []
    filepath = os.path.join(root, 'design_btor.btor')
    filespaths.append(filepath)#add the init file into the paths to be tested
    for i in linenum:
        t = linenum.index(i)
        newname = Filesname(name , t)  #newnames the file design_btor_new2_n.btor
        with open(root + '/'+ newname,'w',encoding='utf-8')as g:
            filepath = os.path.join(root, newname)
            filespaths.append(filepath)
            for ii in range(len(file_list)):
                if ii == i:  
                    line = linechange[t]
                else:
                    line = file_list[ii]                         
                g.write(line)
    return filespaths # new2_n files filepaths and the init files

def main():
    file_list,linenum,linechange,linenotchange= GETfile(path)
    print(linechange)
    GETfile_mod(file_list,linenum,linechange,name,root)


if __name__=='__main__':
    for i in list_all:
        if i not in list_test:
            list_notap.append(i)
    print('these never appear:',list_notap)

    parser = argparse.ArgumentParser()
    parser.add_argument('test_case', action='store', type=str)
    args=parser.parse_args()
    for root, dirs, files in os.walk(args.test_case, topdown=False):
        for name in files:
            if(name.find('btor_new.btor') >= 0):
                path = os.path.join(root, name)
                print(path)
                main()

