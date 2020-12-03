#!/usr/bin/python3

#import sys,subprocess
#sys.path.append('/cm/shared/scripts/modules') #for HOST ONLY
#
#import colored
##declare program name and type
#THIS_PROGRAM_NAME='/cm/shared/scripts/python/wswapAtomID.py'
flag = True
err_msg=''

org_file = input("Please input file name:")
org_file.strip()

if not org_file:
  print(org_file," does NOT exist. Please rerun the program.")
  flag = False
  if len(err_msg)==0:
    err_msg = org_file+" does not exist"
  else:
    err_msg = err_msg+"; "+org_file+" does not exit"
else:
  new_file = "new_"+org_file
  
  f = open(org_file,'r+')
  nf = open(new_file,'w+')
  line = f.readline().rstrip()
  values = []
  head_flg = True
  i = 0
  id_flg = True
  while line:
    if head_flg:
      #nf.write('{0}\n'.format(line.rstrip()))
      i += 1
      if i == 2: head_flg = False
      nf.write('{0}\n'.format(line))
    else:
      values = line.split()
      if values[0] == "timestep":
        head_flg = False
        nf.write(line+'\n')
        #read following three lattice parameters and write it into new file
        line = f.readline().rstrip()
        #nf.write('{0:36s}\n'.format(line))
        nf.write(line + '\n')
        line = f.readline().rstrip()
        nf.write(line + '\n')
        line = f.readline().rstrip()
        nf.write(line + '\n')
      else:
        if id_flg:      #if it is atom id line, swap the 2nd and 3rd column
          id_flg = False  # next line would be coordinations
          nf.write("{0:>8s}{2:>10d}{1:>12d}{3:>12.6f}\n".format(values[0],int(values[1]),int(values[2]),float(values[3])))
        else:
          id_flg = True   # next line would be atom id line
          nf.write(line+'\n')
    line = f.readline().rstrip()

  print("Successfully swapped the atom IDs and generated a new file:",new_file)





#log='command'
#com=open(log,'w')
#com.write("run "+THIS_PROGRAM_NAME+" status:"+flag)
#com.close()

