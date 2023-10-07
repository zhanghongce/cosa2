#btorline -> get uut line -> vector 
#def line-to-vec   
#def get-mentioned-line-num , sign uut line , return line
# def BTOR_new : get the indexs ,then write the new btor
#aid uut: add uut to all uut get related line
#btor_0: onvert uut to btor files
#btor_1: run the files in btor_0

import os,sys
import subprocess
import argparse
def filesname(name):
    b = '_'+ 'new'
    i = name.find('.btor')
    newname = name[:i] + b + '.btor'
    return newname

'''def Process_uut(i,line,uut_mod = []):
    if i in uut_list and i not in uut_mod:
        position = line.find(";")
        line = line[:position]
        list_line = line.split()
        list_line.append('*uut\n')
        line = ' '.join(list_line)ssss
    return line, uut_mod'''


def GETfile():#get wrapper.uut list
    #operator_list = []
    init_file = []
    uut_list = [] #the index of the line
    with open(path,'r')as f:
        while True:
            line= f.readline()
            list_line = line.split()
            init_file.append(list_line)
            if 'wrapper.uut' in line:
                uut_list.append(list_line[0])
            if not line:break # if there is no break ,this is a dead loop
    print('before iteration: ',len(uut_list))
    return init_file,uut_list
    
        #print(uut_list)
        #print(len(uut_list))
            #print(list_line[1])
            #if list_line[1] not in operator_list:##get operator list
            #   operator_list.append(list_line[1])

def UUT_index(index,filelist,uut_list_all,uut_inter):#get the index related to one index
        #print(index)tad 
        vector = filelist[index]
        uut_inter.append(vector[1])
        deindex = UUT_line(vector)
        if deindex[0]  == '000' and len(deindex) == 1 :
            pass
        else:
            for ii in deindex:
                if ii not in uut_list_all:
                    uut_list_all.append(ii)
                    UUT_index(int(ii),filelist,uut_list_all,uut_inter)
        return uut_list_all,uut_inter


def BTOR_new(uut_list_all,init_file):#get the new btor
    newname = filesname(name)
    with open(root + '/'+ newname,'w',encoding='utf-8')as g:
        while True:
            for vector in init_file:
                line = ' '.join(vector)
                #print('this is line:',line)s
                if len(vector) >=1 and vector[0] in uut_list_all :# process the line related to inituut  
                    if';' in line:
                        position = line.find(";") 
                        line = line[:position-1] + '*uut\n'
                    else:line = line + '*uut\n'
                elif len(vector) >=1 and vector[0] not in uut_list_all:
                    line = line + '\n'
                else:pass
                g.write(line)
            if not line:break

def UUT_line(vector):
    list_sort = ['sort','input','const','state']# no index
    list_state = ['constraint','bad']#only index
    list_normal2 = ['not','redor','redand']
    list_normal3 = ['init','next','eq','or','add','ult','and','concat','neq','sub','slt','sra','sll','xor','read','ugte','srl','ugt']
    list_normal4 = ['ite']
    list_ignore = ['BTOR','end']
    #uext,sext,slice,write
    relate_index = []
    if vector[1] in list_sort:
        return ('000',)
    if vector[1] in list_state:
        return (vector[2],)
    if vector[1] == 'uext':
        return (vector[3],)
    if vector[1] == 'sext':
        return (vector[3],)
    if vector[1] == 'slice':
        return vector[2], vector[3]
    if vector[1] == 'write':
        return vector[2], vector[3], vector[4], vector[5]
    if vector[1] in list_normal2:
        return (vector[3],)
    if vector[1] in list_normal3:
        return vector[3], vector[4]
    if vector[1] in list_normal4:
        return vector[3], vector[4], vector[5]
    if vector[1] in list_ignore:
        return ('000',)
    else:
        print('an unknown operator appears ', vector)
        return ('000',)
 
def CHECK_eq(uut_allinall):
    vector = uut_allinall[0]
    for vec in uut_allinall:
        for v in vec:#the locat in the lists,268
            if v in vector:
                pass
            elif v not in vector:
                print(type(v))
                print('this is not found: ',v)

def main():
    init_filelist,uut_list= GETfile()
    #print(uut_list)
    uut_list_all = uut_list.copy()
    uut_inter_all = []#for one file
    #with open('./modbtor/'+'uutlocat' ,'w',encoding='utf-8')as g:
    for i in uut_list:
        uut_inter = []
        uut_list_all,uut_inter = UUT_index(int(i),init_filelist,uut_list_all,uut_inter)
        uut_inter_all.append(uut_inter)
            #line = i + ' this is uut: '+ str(uut_inter) + '\n'
            #g.write(line)
    #print(uut_inter)
    print('after iteration: ',len(uut_list_all))
    BTOR_new(uut_list_all,init_filelist)
    return uut_inter_all

'''def main():
    uut_inter_all = main_0()
    CHECK_eq(uut_inter_all)'''

if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('test_case', action='store', type=str)
    args=parser.parse_args()
    uut_allinall = []
    for root, dirs, files in os.walk(args.test_case, topdown=False):
        print (root)
        for name in files:
            if(name.find('btor.btor') >= 0):
                path = os.path.join(root, name)
                uut_inter_all = main()
                uut_allinall.append(uut_inter_all)
    CHECK_eq(uut_allinall)    
            
                