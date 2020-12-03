#!/usr/bin/python

import sys, subprocess, os
sys.path.append("/cm/shared/scripts/modules") #for HOST ONLY
from datetime import datetime as dt

import colored
#declare program name and type
THIS_PROGRAM_NAME=__file__

TOTAL = int(20000001)

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

spc_tot = {}
spc_avg = {}
spc_modf_tot = {}
spc_modf_avg = {}
for key in SPCS.values():
  spc_tot[key] = 0
#  spc_avg[key] = 0
  m_key = key + "*"
  spc_modf_tot[m_key] = 0
#  spc_modf_avg[m_key] = 0

filename = input("Input file name: ")
filename = filename.strip()

if os.path.isfile(filename):
  flag = True
else:
  flag = False

if flag:
  with open(filename,"r") as f:
    line = f.readline().strip()
    count = 0
    while line:
      vals = line.split()
      if vals[0].isnumeric():
        spc_tot[vals[1]] += int(vals[3])
        m_key = vals[1] + "*"
        spc_modf_tot[m_key] += int(vals[-2])
      else:
        count += 1
      line = f.readline().strip()

    for key in spc_tot.keys():
        m_key = key + "*" 
        print(count,"spc_tot[",key,"]=",spc_tot[key],"avg(per spc)=", round(int(spc_tot[key])/count,3), "avg(per spc*troj)=", round(int(spc_tot[key])/count/TOTAL,3), "\tspc_modf_tot[",m_key,"]=",spc_modf_tot[m_key], "avg(per spc)=", round(int(spc_modf_tot[m_key])/count,3), "avg(per spc*troj)=", round(int(spc_modf_tot[m_key])/count/TOTAL,3))


else:
  print(filename + " does not exist.\n")



#write to log file
log='command'
com=open(log,'a')
if flag:
  com.write(dt.now().strftime("%m/%d/%Y %H:%M:%S")+__file__ + "status: Successful\n")
else:
  com.write(__file__ + "status: Failed\n")
com.close()

