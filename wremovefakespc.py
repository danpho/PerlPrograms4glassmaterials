#!/usr/bin/python

import sys,subprocess,os
sys.path.append("/cm/shared/scripts/modules") #for HOST ONLY

import colored
from datetime import datetime as dt

# function to clean tempory files
def clean_file(FileName):
  def_tmp_file=FileName
  if os.path.isfile(def_tmp_file):
    cmd = "rm -fr "+def_tmp_file
    os.system(cmd)
    print(def_tmp_file," was existing and has been deleted.")
  return 1
# function to show the species name 
SPCS={}
SPCS['Ac'] = "Al-OH"
SPCS['Th'] = "Al-OH2"
SPCS['La'] = "Si-OH"
SPCS['Ce'] = "Si-OH2"
SPCS['Ne'] = "H3O"
SPCS['Ar'] = "OH"
SPCS['D']  = "H2O"
SPCS['Re'] = "O-X"
SPCS['Pr'] = "Si-OH-Si"
SPCS['Yb'] = "Si-OH-Al"
SPCS['Pa'] = "Al-OH-Al"
SPCS['Sg'] = "X-Sg(Z)-Y"
def SpeciesName(element):
  if element == 'Ac': return("Al-OH")
  elif element == 'Th': return("Al-OH2")
  elif element == 'La': return("Si-OH")
  elif element == 'Ce': return("Si-OH2")
  elif element == 'Ne': return("H3O")
  elif element == 'Ar': return("OH")
  elif element == 'Re': return("O-X")
  elif element == 'Pr': return("Si-OH-Si")
  elif element == 'Yb': return("Si-OH-Al")
  elif element == 'Pa': return("Al-OH-Al")
  elif element == 'Sg': return("X-Sg(Z)-Y")
  else: return("out of list")

#set flag to conduct program
flag = True
#declare program name and type
#THIS_PROGRAM_NAME=__file__

print("This program " + __file__ + " is used to find 'faked' species in which one hydrogen atom bonds two oxygen atoms.\n")

file_full_name = input("Input labeled file name: ")
file_full_name.strip()
file_name, file_ext  = os.path.splitext(file_full_name)
print("filename=",file_name,"\t extension=",file_ext)

spc = input("Input species name (default 'H'): ")
if len(spc) > 0:
  spc = spc.strip()
else:
  spc = 'H'
#print("spc=",spc)

if os.path.isfile(file_full_name):
  flag = True
  tgt_id = file_full_name.split("_")[0] #target atom id
else:
  flag = False

if flag:
  #define dictionary to count target species
  # In case error happened, two methods are implemented for verification
  SPCS_TGT = {}
  SPCS_MDF_NEAR_TGT = {}
  for key in SPCS.keys():
    SPCS_TGT[key]=0
    m_key=key+"*"
    SPCS_MDF_NEAR_TGT[m_key]=0
#  SPCS_TGT['Ac']=0
#  SPCS_TGT['Th']=0
#  SPCS_TGT['La']=0
#  SPCS_TGT['Ce']=0

#  SPCS_TGT['Ac*']=0
#  SPCS_TGT['Th*']=0
#  SPCS_TGT['La*']=0
#  SPCS_TGT['Ce*']=0
#  SPCS_MDF_NEAR_TGT['Ac*']=0
#  SPCS_MDF_NEAR_TGT['Th*']=0
#  SPCS_MDF_NEAR_TGT['La*']=0
#  SPCS_MDF_NEAR_TGT['Ce*']=0
   
  v_spcs_tgt = SPCS_TGT   # for verification purpose

  # collect Primary frame info which can show the species at each trojectory
  tmp_file = file_name + ".tmp"
  clean_file(tmp_file)

  #for tgt_spc in SPCS_TGT.keys():
  #cmd = "grep -E 'FRAM.*" + tgt_spc + "' " + file_full_name + " >> " + tmp_file
  cmd = "grep -E 'FRAM' " + file_full_name + " >> " + tmp_file
  os.system(cmd)

  #find species not in the list and add them in dictionary
  with open(tmp_file,"r") as f:
    line = f.readline().strip()
    while line:
      vals = line.split()
      i = 7
      while i < len(vals):
        if (not vals[i] in SPCS_TGT.keys()) and (vals[i] != spc) and vals[i].isalpha():
          SPCS_TGT[vals[i]] = 0
          SPCS_MDF_NEAR_TGT[vals[i]] = 0
        i += 1 
      line = f.readline().strip()
  f.close()
  print(SPCS_TGT, SPCS_MDF_NEAR_TGT)
  # count the number of trajectory 
  cmd = "grep 'FRAM' " + file_full_name + "|wc -l > tmp"
  os.system(cmd) 
  f = open("tmp",'r')
  total = int(f.readline())
  print("total=", total)
  f.close()

  #read unique spc ids
  file_name_cnt_spc = "./cnt_aloh/"+file_name + "amt_transit_spc.dat"
  clean_file(file_name_cnt_spc)
  with open(file_name_cnt_spc,'a') as f_amt:
    with open(tmp_file,'r') as pfrm:
      line = pfrm.readline().strip()
      h_ids = {}
      while line:
        if spc in line:
          val = line.split()
          i = 0
          while i < len(val):
            if val[i] == spc:
              if val[i-1] in h_ids.keys():
                pass
              else:
                h_ids[val[i-1]] = 0
            elif val[i] in SPCS_TGT.keys():
              SPCS_TGT[val[i]] += 1
            elif val[i] in SPCS_MDF_NEAR_TGT.keys():
              SPCS_MDF_NEAR_TGT[val[i]] +=1 
            else: 
              pass
            i+=1
        line = pfrm.readline().strip()
      print("The number of unique ",spc," bonded to ",tgt_id," is ",len(h_ids),". They are ", h_ids.keys())
      print("Species number:", SPCS_TGT,"modifers nearby: ", SPCS_MDF_NEAR_TGT)
      f_amt.write(str(len(h_ids))+"\n")
    pfrm.close()
  f_amt.close()

  #analyze spc neighbors
#  clean_file(tmp_file)
#  for id in h_ids.keys():
#    tmp_file = file_name+".tmp"
#    cmd = "grep -E 'SBSDRYTGT\s+"+id+"\s+H' " + file_full_name + " >> " + tmp_file
#    os.system(cmd)
#    cmd = "tail -n 5 "+tmp_file
#    os.system(cmd)
  
  # write to output file
  output_file=file_name + ".spc_count.dat"
  clean_file(output_file)
  with open(output_file,"a") as output:
    output.write("("+file_full_name+")")
    output.write("tgt_spcID\tspc\ttot_amt\tavg_amt\tspc(CaNBY)\ttot_amt\tavg_amt\n")
    for key, val in SPCS_TGT.items():
      if key in SPCS.keys():
        species = SPCS[key]
        m_key = key+"*"
        output.write(tgt_id+"\t"+species + " : " + str(val) + "\t" + str(round(val/total,3)) + "\t" + species + "* : " + str(SPCS_MDF_NEAR_TGT[m_key])+ "\t" + str(round(SPCS_MDF_NEAR_TGT[m_key]/total,3)) + "\n")
      
      
else: #flag is false
  print("Error occurred. Please check the log file.\n")

#clean temp files
cmd = "rm -fr tmp *.indv.tmp"
os.system(cmd)


#write to log file
log='command'
com=open(log,'a')
if flag:
  com.write(dt.now().strftime("%m/%d/%Y %H:%M:%S")+__file__ + "status: Successful\n")
else:
  com.write(__file__ + "status: Failed\n")
com.close()



