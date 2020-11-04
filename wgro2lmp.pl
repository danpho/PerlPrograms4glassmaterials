#!/usr/bin/perl -w
#/*====================================================
#
# Author: Liaoyuan Wang    
# Email: wly_ustc@hotmail.com  
#  @ Copyright @  belongs to Liaoyuan Wang.
#  @ However, you can NOT copy to the
#  @ other machines without Dr. Wang's permission 
#  @ or use it in commercial purpose. Any question,
#  @ please contact with Dr. Wang. 
# Created by:     2019-09-06 22:45
# Last modified:	2019-09-07 12:31
#
# Filename:		wgro2lmp.pl
#
# Description:
#
#=====================================================*/
#set the strict condition;
#2019-09-06 22:45 Found lattice constants in each frame are not same
#2019-09-07 12:31 fixed
#
use strict;
use warnings;#give a warning message when error occured
use diagnostics; #When you do not understand the warning message, use it to learn more info.It cost a lot of resource!
use Scalar::Util qw(looks_like_number);   #used to test numeric value. OR if ($var =~ /^[+-]?/d+/$/ ){...}
use List::MoreUtils qw(first_index);
use Term::ANSIColor; #Set the text color for output. color: red, cyan, green, yellow, blue,CLEAR, RESET, BOLD, DARK, UNDERLINE, UNDERSCORE, BLINK, REVERSE, CONCEALED, BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE, ON_BLACK, ON_RED, ON_GREEN, ON_YELLOW, ON_BLUE, ON_MAGENTA, ON_CYAN, and ON_WHITE 
#    print color 'bold blue';
#    print "This text is bold blue.\n";
#    print color 'reset';
#    print "This text is normal.\n";
#    print colored ("Yellow on magenta.", 'yellow on_magenta'), "\n";
#    print "This text is normal.\n";
#    print colored ['yellow on_magenta'], 'Yellow on magenta.';
#    print "\n"; \n";

use tm;     #tm::trim(...)
use chm;    #provide info of elements, charge 

$"=";";     #allow to use ";" to seperate arrays when print an array which is quoated, e.g. print "@\n";
 ####################################################################################
#  Gro file is a large file. To save scanning time, BASH commands are used         #
#  Following is the basic steps                                                    #
#  s1.1: get head section for lammps data file,                                    #
#   such as, notation,#of atoms,#of atom types, box size, Masses                   #
#   This info get from different part in the gro file. The script looks massy.     #
#  s1.2: get the coordinates associated with charge (0 or default settings)        #
#     this will be stored in a tmp file                                            #
#  s2: append the tmp file to the head section to get lammps input data file.      #
####################################################################################
#  This scripts has been improved. It requires gro file only.                      #
####################################################################################

my $PROGRAM=$0;
#system("source ~/.bash_profile;set -o posix;set | grep 'SCRIPTS';");
my $CONV_FILE="gro2lammps.dat";   #filename in which converted input data are stored
my $ATOM_NAME_LENGTH = 3;         #In gro file, the 1st column (from the 3rd line)includes atom id and atom name.  Currently, the length of atom name is 3
my $TYPE_INDX=0;        #store the column number of type from elements.h
my $ELEMENT_INDX=1;     #store the column number of element name from elements.h
my $MASS_INDX=2;        #store the column number of mass value from elements.h. NOTE:INDEX starts from 0 in PERL.
my $CHARG_INDX=3;       #store the column number of charge value read from elements.h
my $DEFAULT_CHG="0.000";#if charge in elements.h is not set, use this value. here use string for sed using
my $DFT_AMT_FRM_SAMPLES=201;    # take 201 frames to analyze zdp, bad,...
#my $PATH_SCRIPTS= `(set -o posix;set | grep SCRIPTS)`;
#print "PATH_SCRIPTS=$PATH_SCRIPTS\n";

my $flag=1;             #1:true,program can run;0:program quitting if some errors, such as missing parameters, file/directory not    existing
my $scripts_dir;        #scripts and .h file location

print colored("$PROGRAM","bold cyan")," is used to convert the last structure in gro file into lammpstrj file which can be used to run LAMMPS program.\n\n";

my $host=`hostname`;chomp($host);
@_=split(/\./,$host);
if(lc($_[0]) eq "bustard")
{$scripts_dir="/cm/shared/scripts/";}
elsif(lc($_[0]) eq "bunsen")
{$scripts_dir="/Volumes/Bunsen_HD2/Simulation/wly/bin/scripts";}
else
{ print "Please sepcify the path for element.h file";
  $_=<STDIN>;
}

if(not -e $scripts_dir)
{ print colored("Warning","bold yellow blink"),"$scripts_dir does NOT exist. WILL QUIT after checking other files.\n";
  $flag=0;
}
{$flag=1;}

my $work_path=tm::trim(`pwd`);
my $line;               #store data of a line
my @values;             #store value of each column
my @sub_values;
my $tmp;                #temporarily store some values
my $gro_suffix="gro";
my $his_suffix="His";
my $control_file="0analysis";
my $file_name='';          #store file name
my $gro_file;
my $gro_tmp_file;
my $his_file;
my $lmp_file;
my $i;my $j;my $k;      #loop control
my $flag_del=0;         #if there are errors, tmp file will not be deleted for debug
my $struc_file="structure.dat";  #structure file for bond analysis.
my $tot_amt_frm;        #total amount of frames in gro file
my $amt_sampling;       #sampling amount for analysis
my $first_sampling_no;  #first frame no of sampling
my $first_line_sampling;  #first line no for sampling file which is a temp file
my $last_line_sampling;   #last line no for sampling file which is a temp file
#my $gulp_file="gulp.dat";        #gulp file for bond analysis

# Begin
### 0analysis is a control file. It contains the file name without suffix
# read file name from 0analysis
if(not -e "0analysis")
{  print colored("control file 0analysis","bold cyan")," does not exist. \n\n";
   print "You may use different name. Do you want to manually input the control file name? (y/n, ENTER for no)\t";
   $_=<STDIN>;      #y/n/ENTER
   chomp($_);
   $_=~s/^\s+|\s+$//g;
   if (lc($_) eq 'n' or lc($_) eq 'no' or length($_)==0){print "User choose not to input control file. User can manually input gro file later.\n";$flag=0;}
   else
   {  print"Input the file name:";
      $line=<STDIN>;chomp($line);
      if(not -e $line){$flag=0;print colored("$line does NOT exist. Quit!\n","bold yellow");}
   }#end else if (lc($_) eq 'n' or lc($_) eq 'no')
}#end if (not -e "0analysis")
else
{ $flag=1;
  ########################################################################
  #### below is the script to get gro file name from 0analysis.
  #only get the section beteen PROPERTIES and end. output it to a temp file
#  system("cp 0analysis 0analysis.bak");  #debian always delete origin file while using sed command
  system("sed -n '/PROPERTIES/,/end/w 0analysis_g2l.tmp' 0analysis");
  open (FILENAME,"<0analysis_g2l.tmp");
  $i=0;
  while($line=<FILENAME>)
  {
     $i++;
     #to get gro and history file name from 0analysis
     if ($i == 6)      #Here, the 6th line contain gro and history file name
     {
        chomp($line);
        $line=~s/^\s+|\s+$//g;
        @values=split(/\s+/,$line);
        $_=$#values;
        $_--;
        $file_name="$values[$_].$gro_suffix";
     }#end if($i==6)
  }#end while($line=<FILENAME>)
  close(FILENAME);   
}#end else of if(not -e "0analysis") 
close(FILENAME);

if(length($file_name)==0)
{
  $_=`ls *.gro |wc -l`;chomp($_);
  system("ls *.gro");
  if($_>1)        #more than one gro file, ask user to choose
  { $_=`ls *.gro`;chomp($_);
    print "Input one of above gro files with suffix(.gro): ";
    $line=<STDIN>;
    chomp($line);
    $line=~s/^\s+|\s+$//g;
    @values=split(/\.gro/,$line);
    if($values[0]=~ /gro/){$file_name=tm::trim($values[0]);}
    else{$file_name="$values[0].$gro_suffix";}
    if(-e $file_name){$flag=1;}
    else{print"$file_name does NOT exist! Quit.\n";}
  }#end if($_>1)
  elsif($_==1)    #only one gro file, automatically choose
  {
    $_=`ls *.gro`;$_=tm::trim($_);
    print "Input gro file name (ENTER for existing $_):";
    $line=<STDIN>;chomp($line);
    if(length($line) eq 0){$file_name=$_;$flag=1;}    #existing gro file
    else                                      #user input
    { $file_name=$line;
      if(not -e $file_name)
      {print "$file_name does NOT exist. Using the unique existing file or CTRL+Z to quit.\n";$file_name=$_;}
    }
  }#end elsif($_==1)
  else
  {$flag=0;print colored("gro file does not exist. Quit!\n","bold yellow");}
}#end if(not -e $file_name)

print "gro file name is $file_name\n";



########## converting gro file to lammptrj file####################
if ($flag==0){print "Required files does not exist. Quit!\n";}
else
{
  #get gro and history file name with suffix   
  $gro_file="$work_path/$file_name";
  $gro_tmp_file="$work_path/$file_name.tmp";
  $his_file="$work_path/$file_name.$his_suffix";
  $lmp_file="$work_path/$file_name.lammpstrj";
  if(-e $his_file){  print "$gro_file\t$his_file\n";}

  my $atom_no;my $atom_type=0;
  my $x_lo=0.0;   my $x_hi;  #unit is angstrom
  my $y_lo=0.0;   my $y_hi;
  my $z_lo=0.0;   my $z_hi;
  my $x;my $y;my $z;
  my $line_starting_frame;
  my $line_ending_frame;
  my @list_line_no_frame;     #list lst line no for each frame
  my @elements;               #unique elements in frames
  my @charge;                 #charges 
  my @types;                  #types of elements 
  my $flg_lattice;            #flag for comparison of lattice constant. If x(frame#1)!=x(frame#1),=0 (same for y, z); if equal, =1
  my @time;                   #save time value in the 1st line of each trojectory
  my @lattice;                #string with all x,y,z
  my @xxx;                    #parse each element in @lattice, and save to the corresponding xxx/yyy/zzz arrays
  my @yyy;                    #parse each element in @lattice, and save to the corresponding xxx/yyy/zzz arrays
  my @zzz;                    #parse each element in @lattice, and save to the corresponding xxx/yyy/zzz arrays
  my $timestep_gap;           #timestep or time gap between two trojactories
  my $indx_frm;               #record frame number when starting conversion

  # get time info and line number for the first line in each trojectory
  $line=`awk '/t=/ {print \$0" @"NR}' $gro_file`;
  @values=split(/\r|\n/,$line);
  $i=0;
  foreach $line (@values)
  { if($line =~ /t=\s+/){;}
    @sub_values=split(/@|\s+/,$');chomp(@sub_values);
    $time[$i]=int($sub_values[0]);
    $list_line_no_frame[$i]=$sub_values[$#sub_values];
    $i++;
  }
  
  if(scalar(@time)>2){$timestep_gap=$time[1]-$time[0];}
  else{$timestep_gap=0;}    #only one trojactory

  # get lattice info
  $line=`awk '{if(NF == 3){print}}' $gro_file`;
  @values=split(/\r|\n/,$line);
  $i=0;
  foreach $line (@values)
  {
    $line=tm::trim($line);
    @sub_values=split(/\s+/,$line);
    $xxx[$i]=$sub_values[0];
    $yyy[$i]=$sub_values[1];
    $zzz[$i]=$sub_values[2];
    $i++;
  }#end foreach $line (@values)
  $tot_amt_frm=$i;


  ##########################################################
  #Here, the history file is not required since gro file can provide box size
  #No evidence proves that the box size in each frame is different from the others
  #here, output a message to ask users check the values
  
  if($tot_amt_frm > $DFT_AMT_FRM_SAMPLES)
  { print "Total frame number in $gro_file is ",colored("$tot_amt_frm","bold cyan"),". Do you want to input sampling size?(ENTER for Yes)";
    $_=<STDIN>;$_=tm::trim($_);
    if(length($_)==0 or (uc($_) eq "Y" or uc($_) eq "YES"))
    { print "Please input sampling size (ENTER for $DFT_AMT_FRM_SAMPLES)";
      $amt_sampling=<STDIN>;
      chomp($amt_sampling);
      if(length($amt_sampling)==0){print "User choose to use default value.\n";$amt_sampling=$DFT_AMT_FRM_SAMPLES;}
      elsif(not $amt_sampling=~ /[0-9]/)
      { print "Invalid input. Using default value $DFT_AMT_FRM_SAMPLES.\n";
        $amt_sampling=$DFT_AMT_FRM_SAMPLES;
      }#end if(not $amt_sampling=~ /[0-9]/)
      else{print "User input value is $amt_sampling.\n";}
    }#end if(length($_)>0)
    else
    { print "User choose not to set sampling size. Will use $tot_amt_frm.\n";
      $amt_sampling=$tot_amt_frm;
    }#end else of if(length($_)>0)
  }
  else
  {$amt_sampling=$tot_amt_frm;}
  
  print colored("sampling size=$amt_sampling\ttot=$tot_amt_frm\n","bold magenta");
  print colored("NOTE:","BOLD YELLOW"),"The first frame starts from 0.\n";
  print "Please input the first sampling number (ENTER for the last $amt_sampling):";
  $_=<STDIN>;  chomp($_);
  $first_sampling_no=$tot_amt_frm-$amt_sampling;
#print"304:\$first_sampling_no=$first_sampling_no\n";<>;
  if(length($_)==0){print "User input choose the last $amt_sampling starting from $first_sampling_no.\n";}
  elsif($_>$first_sampling_no){print"Input would results in out of range. Use default last $amt_sampling starting from $first_sampling_no.\n";}
  else{$first_sampling_no=$_;}

  #here, first_sampling_no is also the index of $list_line_no_frame
  $first_line_sampling=$list_line_no_frame[$first_sampling_no];   #get the first line no of sampling
  $_=$first_sampling_no+$amt_sampling;
  if($_<$tot_amt_frm)                                             #get the last line no of sampling
  {$_++,$last_line_sampling=$list_line_no_frame[$_];}
  else
  {$last_line_sampling=tm::trim(`wc -l <$gro_file`);}
#print"291: \$first_line_sampling=$first_line_sampling,\$last_line_sampling=$last_line_sampling\n";<>;
#  system("sed -n '$first_line_sampling,$last_line_sampling p' $gro_file > $gro_tmp_file;");
#  system("grep t= $gro_tmp_file");
  print colored("1st_sampling=$first_sampling_no\tamt_sampling=$amt_sampling\ttot_amt=$tot_amt_frm\n","bold magenta");

  # there are two situations: charged or not,
  # here, set a flag to control later
  my $flag_charge=1;   # 0: no charge; 1: charged
  print "Do you want each atom be charged?(y/n,default yes)";
  $_=<STDIN>;
  chomp($_);
  $_=~s/^s+|s+$//g;
  if (lc($_) eq 'n' or lc($_) eq 'no')
  {$flag_charge=0;}
  else{$flag_charge=1;}

    
  # scan whole gro file to get 
  # 1. all elements stored in element[k],....
  # NOTE:the index j will be the element_id. So j>=1
  # 2. output atom_ID, element_id, charge, x, y, z to a temparary file which will be appended into lammps data file

  my $flag_frame;    #to store the first line of each frame
  my $atom_amt;
  my $atom_id;       #$atom_id and $atom_name from the first column in gro file.
  my $atom_name;
  my $timestep;
  my $size_frame;         #how many lines in one frame. Used to control output headlines to lammpstrj file
  my $index;         #index for elements, charge, and types
  $size_frame=($last_line_sampling-$first_line_sampling+1)/$amt_sampling;
  #to get how many and what type of elements in gro file
  $i=$list_line_no_frame[$#list_line_no_frame]+2;    # first atom line in the last frame/trojactory
  $j=`wc -l < $gro_file`;chomp($j);
  $j=$j-1;                                            # last atom line in the last frame/trojactory
  
  $tmp=`sed -n '$i,$j p' $gro_file | sort -u -k 1.11,1.15 |sort -n -k 1.16,1.20 |awk '{print \$2}'`;
  chomp($tmp);
  @elements=split(/\r?\n/,$tmp);
  unshift @elements, '';              #type number is same to the index of elements. Thus, add one empty element as $elements[0].
  print "elements:@elements\tlines in one frame=$size_frame\n";
  $k=1;
  #foreach $tmp (@elements)
  for ($k=1;$k<=$#elements;$k++)
  { $tmp=$elements[$k];
    chomp($tmp);
    $_=$chm::ELEMENT_CHG{$tmp};
    $charge[$k]=tm::trim($_);
    $types[$k]=$k;
  } 

  ### above codes collect all required parameters
  # to save file handling time, read target trojatoried into a temporary file $gro_tmp_file
  system("sed -n '$list_line_no_frame[$first_sampling_no],\$ p' $gro_file > $gro_tmp_file;"); 
  print "Check above! Convert from line $list_line_no_frame[$first_sampling_no] in $gro_file.\n";
  open(GRO2LMPS,">$lmp_file") or die "cannot open it for write";
  select GRO2LMPS; $| = 1; select STDOUT;         #use unbuffemiles i/o
  open(GRO,"<$gro_tmp_file");
  $i=0;       #record line number
  $indx_frm=$first_sampling_no-1;       #record frame number
  while($line=<GRO>)
  {
    $i++;
    @sub_values=split(/\s+/,$line);

    if(($i%$size_frame)==1)                             #in gro file, the 1st line of a frame in which shows the timestep info
    { #@sub_values=split(/t=/,$line);
      $indx_frm++;         #frame amount +1
      $timestep=tm::trim($sub_values[$#sub_values]);
      $timestep=int($timestep);
      print colored("Coverting frame labelled with timestep $timestep\n","bold cyan");
      print GRO2LMPS "ITEM: TIMESTEP\n$timestep\n";         #in lammpstrj file, the 1st and 2nd line
    }
    elsif(($i%$size_frame)==2)                          #in gro file, the 2nd line of a frame in which shows the atom amount
    { $atom_amt=$sub_values[0];
#print"372: frame #=$indx_frm\tt=$time[$indx_frm]\tx=$xxx[$indx_frm]\ty=$yyy[$indx_frm]\tz=$zzz[$indx_frm]\n";<>;
      @values=split(/\s+/,$tmp);
      $x_hi=$xxx[$indx_frm]*10;
      $y_hi=$yyy[$indx_frm]*10;
      $z_hi=$zzz[$indx_frm]*10;
#print"377:\$x_hi=$x_hi\t\$y_hi=$y_hi\t\$z_hi=$z_hi\n";<>;

      print GRO2LMPS "ITEM: NUMBER OF ATOMS\n$atom_amt\n";  #in lammpstrj file, the 3rd and 4th line
      print GRO2LMPS "ITEM: BOX BOUNDS pp pp pp\n";         #in lammpstrj file, the 5th line
      print GRO2LMPS "$x_lo $x_hi\n";                       #in lammpstrj file, the 6th line, x range for simulation box
      print GRO2LMPS "$y_lo $y_hi\n";                       #in lammpstrj file, the 7th line, y range for simulation box
      print GRO2LMPS "$z_lo $z_hi\n";                       #in lammpstrj file, the 8th line, z range for simulation box
      print GRO2LMPS "ITEM: ATOMS id type q xs ys zs\n";    #in lammpstrj file, the 9th line
    }
    elsif(($i%$size_frame)==0)            #in gro file, last line of a frame in which shows box size, do nothing
    {next;}
    else                                                #read coordinates from gro file and write into lammptrj file
    {
      $atom_name=substr($line,11,5);$atom_name=tm::trim($atom_name);
      $atom_id=substr($line,0,5);$atom_id=tm::trim($atom_id);
      #my($index)=grep{$elements[$_] eq $atom_name}(0..@elements-1);
      $j=0;
      foreach $_ (@elements)
      {
        chomp($_);
        if($atom_name eq $_){$index=$j;}
        else{$j++;}
      }#end foreach $_ (@elements)
      $x=$sub_values[$#sub_values-2]*10/$x_hi;
      $y=$sub_values[$#sub_values-1]*10/$y_hi;
      $z=$sub_values[$#sub_values]*10/$z_hi;
      printf GRO2LMPS "%d %2d %4.1f %9.7f %9.7f %9.7f\n",$atom_id,$types[$index],$charge[$index],$x,$y,$z;
      #printf GRO2LMPS "%5d%-5s%5s%5d%8.3f%8.3f%8.3f%8.4f%8.4f%8.4f\n",$atom_id,$types[$index],$charge[$index],$x,$y,$z;
    #2WATER  HW3    6   1.326   0.120   0.568  1.9427 -0.8216 -0.0244
      #printf "$atom_id,$types[$index],$charge[$index],$x,$y,$z\n";$_=<STDIN>;
    }
  }#END while($line=<GRO>)

print colored("$PROGRAM","BOLD CYAN")," converted ",colored("$gro_file","bold cyan")," into ",colored("$lmp_file","bold magenta"),".\n";
}#end else if ($flag == 0)
close(GRO2LMPS);
close(GRO);

system("cp $lmp_file dump.all.lammpstrj");

#clean temporary files
system("rm $gro_tmp_file");

my $date=`date`;chomp($date);
system("echo $date $PROGRAM converted $gro_file into $lmp_file > command");
