#!/usr/bin/perl -w
#/*====================================================
#
# Author: Liaoyuan Wang    
# Email: wly_ustc@hotmail.com  
#  @ Copyright @  belongs to Liaoyuan Wang.
#  @ You can copy, modify and use it 
#  @ in computers of Cormack's group,
#  @ However, you can NOT copy to the
#  @ other machines without Dr. Wang's permission 
#  @ or use it in commercial purpose. Any question,
#  @ please contact with Dr. Wang. 
# Created by:2018-04-07 11:06
# Last modified:2020-10-07 11:06
#
# Filename:wnewslb.pl
#
# Description:
# This program is an alternative improved program of wslab.pl 
# which costs too much time to count speceis due to the algorithm
# 1.run xhst.exe or xhst.auto.exe to get newclst.His file
# 2.scan *.His file and count species and classify to different slab 
#   this algorithm is totally different from wslab.pl which 
#   use "grep" and "wc" to count species in each subhistory file
#=====================================================*/
#2020/10/07, added help function. TESTING

use strict;
use warnings;
use Getopt::Std;

my %args;
getopts('h', \%args);

my $help = "\n
  wnewslb.pl is used to quickly scan and count species in each slab. It  does not generate independent history or DLpoly file for each slab. If you want to see each slab file, please run wslb.pl.

  Two files are required:
  1. control file. You can change the settings in \$CONTROL_FILE. For more details of \$CONTROL_FILE, please run wly scripts.
  2. \$model_info parameters For simulation models which is gerated by     xhst.auto.exe. The initial info should be specified by users.

Will add more info later. 
Here are the procedure and the algorithm of wnewslb.pl  .
S0: copy model_info.log and xhst.dat files into “…./newzdp/XXmstp/” directory. Here, XX is a number, like 4mstp, 8mstp, 4.5mstp, 5.5mstp, or 500kstp.  
LAMMPS simulated and created dump.all.lammpstrj files each of them have different timestamp ranges. The time range is 125ps. Thus, from 0-1ns, we have eight directories listed below:
  500kstp, 1mstp, 1.5mstp, 2mstp, 2.5mstp, 3mstp, 3.5mstp, and 4mstp. Similarly, user can find directories for 2-5ns time range.
We have applied xanal and xhst to analyze the dump.all.lammpstrj file. So we can create xhst.dat and model_info.log files based on our analysis. 
NOTE: Once these two files are created, please do NOT change it to keep the consistence. If you have to change the reference point, PLEAE BACKUP THESE FILES FIRST. After finishing analyzing data using different reference point, user should restore these files back to original ones. 
In this directory, the files have been extracted and split using wdump.pl program.

S1: run wnewslb.pl. program will pre-check required files and the data integrity. It is an interactive phase.
User can choose what to do at the very beginning. 
Program will conduct user to choose required parameters. 
Default values have been set. User can simply click “ENTER” to choose it.

## Below S2-S4 procedures are controlled by wnewslb.pl
#S2: scan atoms in each target slab and count them. 
#
#S3: calculate averaged amount 
#
#S4: output the total and average data
#
#S5: user download all *.statistic.dat files and perform further analysis using different tools.
#
#S6: check “command” file to see the final status and whether there are any errors occurred. This is designed for those analysis without interactive programs which is running in computing nodes. For this analysis, we do not need it. User can see the results directly.
#
LW 
Oct. 07, 2020
";     


#die $help if $args{h};
#LW comment above script because this program is using diagnostics.
#It leads to a warning message "uncaught exception from user code"
#LW use below two scripts instead.
if ($args{h})
{
  print $help if $args{h};
  exit 1;
}

#end help file
######################################
#original program
#set the strict condition;
use strict;
use warnings;#give a warning message when error occured
use diagnostics; #When you do not understand the warning message, use it to learn more info.It cost a lot of resource!
use Scalar::Util qw(looks_like_number);   #used to test numeric value. OR if ($var =~ /^[+-]?/d+/$/ ){...}
use Term::ANSIColor; #Set the text color for output. color: red, cyan, green, yellow, blue,CLEAR, RESET, BOLD, DARK, UNDERLINE, UNDERSCORE, BLINK, REVERSE, CONCEALED, BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE, ON_BLACK, ON_RED, ON_GREEN, ON_YELLOW, ON_BLUE, ON_MAGENTA, ON_CYAN, and ON_WHITE 
#    print color 'bold blue';
#    print "This text is bold blue.\n";
#    print color 'reset';
#    print "This text is normal.\n";
#    print colored ("Yellow on magenta.", 'yellow on_magenta'), "\n";
#    print "This text is normal.\n";
#    print colored ['yellow on_magenta'], 'Yellow on magenta.';
#    scalar(grep $_, @a)

#customerized module by LW
use sys_perl;
use tm;     #module for clean variables. tm::trim(...)
use rc;     #module for read value which may include default one. rc::read_custmz(<info for user(string)>,<value>)

my $SCRIPT_NAME="wnewslb.z.pl";             #program name
my $CONTROL_FILE="xhst.dat";              #default control file
my $MODEL_PARAMETERS="model_info.log";    #default parameters for simulation model
my $DFT_DR=1;                             # default thickness of each slab, unit A
my @ELEMENTS;
my $unit_timestep=0.25;     #unit fs, here should be ?x200, namely there are 201 frames in each file. NOTE: simulation time step is 0.25fs, but LAMMPS extract one frame every 100 timesteps, and each simulation consists of 5000 frames,    one file covers 5000x100x0.25=125000fs=125ps=0.125ns

$ELEMENTS[1]='Ne';$ELEMENTS[2]='Ar';$ELEMENTS[3]='Re';$ELEMENTS[4]='La';$ELEMENTS[5]='Ac';$ELEMENTS[6]='Ce';
$ELEMENTS[7]='Th';$ELEMENTS[8]='Pr';$ELEMENTS[9]='Yb';$ELEMENTS[10]='Pa';$ELEMENTS[11]='Sg';$ELEMENTS[12]='Fe';
$ELEMENTS[13]='Te';$ELEMENTS[14]='Se';$ELEMENTS[15]='O';$ELEMENTS[16]='H';$ELEMENTS[17]='Si';$ELEMENTS[18]='Al';
$ELEMENTS[19]='Ca';


my $flag_avg_tmstp=1; # use average time step or real time step, default =1 average
my $line;             # to store line read from a file
my @values;           # to parse each word in the $line read from a file
my $subline;          # same to $line function
my @sub_values;        # same to @values function
my $tmp;my $subtmp;
my $flag=1;           # flag control. =1: no apparent error; =0:error occured,quit program or not running
my $work_dir=`pwd`;   # current work/analysis directory 
my $mystep;
my $control=$CONTROL_FILE;  # for customerized control file name, currently use default one
my $time_stamp;       # time stamp, like 500kstp, 1mstp,... can be read from $control file or read from the path
my $model_info=$MODEL_PARAMETERS;
my %SPECIES=
(
  NE  => 1,
  AR  => 2,
  RE  => 3,
  LA  => 4,
  AC  => 5,
  CE  => 6,
  TH  => 7,
  PR  => 8,
  YB  => 9,
  PA  => 10,
  SG  => 11,
  FE  => 12,
  TE  => 13,
  SE  => 14,
  O   => 15,
  H   => 16,
  SI  => 17,
  AL  => 18,
  CA  => 19,
);


print "This program ",colored("$SCRIPT_NAME","bold cyan")," is used to quickly scan and count species in each slab. It does not generate independent history or DLpoly file for each slab. If you want to see each slab file, please run ",colored("wslab.pl","bold yellow"),".\n";

print colored("\nNOTE:","BOLD YELLOW BLINK"),colored("Below are required files with notation for each file\n\n","bold yellow");
print colored("$control","bold red"),"  #control file. You can change the settings in $CONTROL_FILE. For more details of $CONTROL_FILE, please run ",colored("wly","bold cyan")," program.\n";
print colored("$model_info","bold red"),"  #parameters for simulation models which is gerated by xhst.auto.exe. The initial info should be specified by users.\n";
print"\n###################### END REQUIRED FILE LISTS ########################\n\n",colored("Please make sure it exists. CTRL+C or CTRL+Z can quit this program.\n","bold cyan");

if(-e $control){$flag=1;}
else{$flag=0;}

if ($flag ==0)
{print "Required file $control or $model_info are missed. Quit program.\n";}
else
{ 
  print colored("Note","bold yellow blink"),": this program can count species in ",colored("1.real time","bold cyan")," and ",colored("2.average time","bold cyan"),". Which do you want to choose ?(ENTER for default 2.average time)";
  $_=<STDIN>;chomp($_);
  if(length($_)==0 or $_ eq 2){$flag_avg_tmstp=1;}
  elsif($_ eq 1){$flag_avg_tmstp=0;}
  else{print "Invalid input, use average time.\n";$flag_avg_tmstp=1;}
  
  #### beginning of parameter configuration #####
  # in this section, will configure time stamp, total thickness of interface box, index for each slab

  #read time stamp
  chomp($work_dir);
  if ($work_dir=~ /kstp/)
  {
    @values=split(/kstp/,$work_dir);
    @sub_values=split(/\//,$values[0]);chomp($sub_values[$#sub_values]);
    $mystep="$sub_values[$#sub_values]kstp";
    $time_stamp=($sub_values[$#sub_values]-500)*1e3;#because the last timestep is 500kstp in lammpstrj file. Here, kstp is the default first initial simulation
  }
  elsif($work_dir=~ /mstp/)
  {
    @values=split(/mstp/,$work_dir);
    @sub_values=split(/\//,$values[0]);chomp($sub_values[$#sub_values]);
    $mystep="$sub_values[$#sub_values]mstp";
    $time_stamp=$sub_values[$#sub_values]*1e6-500*1e3;
  }
  else
  { print "NOT found time stamp (like 500kstp,1mstp..) in current workpath. Will read from control file $control.\n";
    $mystep=`sed -n '14,14 p' $control`;chomp($time_stamp);
    if($mystep=~ /kstp/){$tmp=~ s/\D//g;$time_stamp=$tmp*1e3-$tmp*1e3;}
    elsif($mystep=~ /mstp/){$tmp=~ s/\D//g;$time_stamp=$tmp*1e6-500*1e3;}
  }
  print "time stamp=$time_stamp\n";
  #$_=<STDIN>;

  #### parameter for user to input ####
  my $dr;       # thickness for each slab
  print "Input thickness for each slab (ENTER for $DFT_DR Angstrom)";
  $dr=<STDIN>;chomp($dr);
  if(length($dr)==0){$dr=$DFT_DR;print "User choose default value $dr","A\n";}
  elsif($dr=~ /\d/){print "User input value $dr","A\n";}
  else{print "Invalid input, the default value $DFT_DR","A will be used.\n";$dr=$DFT_DR;}

  #### parameter from xhst.dat ####
  #PERL doesnot support matrix well
  #to speed searching, hush is used to give species index
  #each slab is labeled from 0 to N, where 0 denotes the first layer, ...N denotes the last layer
  #So user do not need to manually set the layer number which is determined by the total thickness and the thickness of each slab
  #use int($z_max-$z)/$dr) to decide which slab the species locates in
  my $top_glass=`sed -n '9,9 p' $control`; chomp($top_glass);             #top surface of glass box at initial structure
  my $bottom_water=`sed -n '10,10 p' $control`;chomp($bottom_water);      #bottom surface of water box at initial structure
  my $gap=$bottom_water-$top_glass;                                       #gap between water and glass box at initial structure
  my $thickness_glass=`sed -n '5,5 p' $control`;chomp($thickness_glass);  #thickness of interface box in glass box;used to define bottom of interface box range
  my $thickness_water=`sed -n '6,6 p' $control`;chomp($thickness_water);  #thickness of interface box in water box;used to define top interface box range
  my $mycomp=`sed -n '15,15 p' $control`;chomp($mycomp);
  my $z_max=$top_glass+$gap+$thickness_water; # PERL does not support negative index for array. Using top surface of interface box instead of top surface of glass as a reference
  my $z_min=$top_glass-$thickness_glass;
  my $tot_thickness=$thickness_glass+$thickness_water+$gap;
  my $indx_max;
  if(($tot_thickness%$dr)==0){$indx_max=int($tot_thickness/$dr);}
  else{$indx_max=int($tot_thickness/$dr)+1;}
  my $size_hash=keys %SPECIES;
  my $flag_newline;       #control format when newline is true, output slab z value
#print "size_hash=$size_hash\tindx_max=$indx_max\tz_max=$z_max\tz_min=$z_min\ttop_glass=$top_glass\n";

  my @filelist;           # lammpstrj file list
  my $lmp_file;           # each lammpstrj file name
  my $newclst_his_file;   # *.newclst.His
  my $tm_slb_spc_file;    # statistic file consits of timeseries and slab and species info
  my $nm_slb_spc_file;    # statistic file consits of timeseries and slab and species info
  my $slb_spc_file;       # at specific time duration, statistic file consists of slab and species info
  my $i;my$j;my$k;        # index for loops

  my $atm_amt_per_frame;  # atom amount in each frame
  my $timestep;           # timestep
  my $time;               # convert timestep to real time. Note, time STAMP and timestep will consider together
  my $z;                  # z value of species

  #using two array to save species name and its amount
  my @species=@ELEMENTS;  # species name, like Ne, Ar,
  my @species_amt;        # species amount
  my %indx_species=reverse %SPECIES;
  my $atom_name;          # atom name 
  my $hash_value;         # hash value, actually index for array, like Ne => 1
  my $amt_his_file;       # amount of newclst.His files
  my $tm_indx;            # index of time 
  my $frame_amt_per_file;
 
  $line=`ls *x*.lammpstrj | sort -n`;
  @filelist=split(/\r?\n/,$line);chomp(@filelist);
  $amt_his_file=@filelist;
#  print @filelist,"\n$amt_his_file\n";


  foreach $lmp_file (@filelist)
  { print colored("Analyzing $lmp_file ","bold cyan");
    $newclst_his_file="$lmp_file.newclst.His";                           #file labels different speces in the interface box. 
    $slb_spc_file="$lmp_file.slb-spc.statistic.dat";
    $nm_slb_spc_file="$lmp_file.nm-slb-spc.statistic.dat";
    open(SPC_CNT,">$slb_spc_file");
    open(NM_SPC_CNT,">$nm_slb_spc_file");
    $_=int($top_glass*100)/100;
    #$_=math::round($top_glass,2);
    print SPC_CNT "time(ps)\tslab(REF:$_","A)\t";
    print NM_SPC_CNT "time(ps)\tslab(REF:$_","A)\t";

    for ($i=1;$i<=(keys %indx_species);$i++){print SPC_CNT "$indx_species{$i}\t"; print NM_SPC_CNT "$indx_species{$i}\t";}
    print SPC_CNT "\n";
    print NM_SPC_CNT "\n";

    @sub_values=split(/\./,$lmp_file);chomp(@sub_values);
    @_=split(/x/,$sub_values[0]);
    $time=$_[0]*5+$time_stamp*.25/1000;      #unit ps, for current file time duration
    print "time=$time ps\n";#$_=<STDIN>;
    $frame_amt_per_file=$_[1]+1;    #each file consists of an initial frame
    $frame_amt_per_file=`grep TIMESTEP $lmp_file |wc -l`;chomp($frame_amt_per_file);
print "check frame amount=$frame_amt_per_file\n";

    #initialize species amount
    for ($i=1;$i<=$size_hash;$i++)
    {for($j=0;$j<$indx_max;$j++){$species_amt[$i][$j]=0;}}

    #read *.newclst.His file and scan all species and then count those ones in z specified range
    #consider to convert it into a function and then scan in x, y direction
    open(NEWCLST,"<$newclst_his_file");
    $i=0;
    while($line=<NEWCLST>)
    {
      $i++; 
      $line=tm::trim($line);
      @values=split(/\s+/,$line);chomp(@values);
      if($i<=2){next;}
      else
      {
        if($values[0] eq "timestep")
        {$timestep=$values[1];$atm_amt_per_frame=$values[2];$j=0;}
        $j++;
        if($j==1 or $j==2 or $j==3 or $j==4){next;}    #skip box size
        else
        {
          if($j%2==1)
          { $atom_name=uc($values[0]);
            #$species_amt[$SPECIES{$atom_name}]++;
          }
          else
          { $z=$values[2];                              #test$_=$z_max-$z;
            $k=int(($z_max-$z)/$dr);
            #print "j=$j\tk=$k\t\$_=$_\tz=$z\t$z_max\n"; #test correct
            $hash_value=$SPECIES{$atom_name};chomp($hash_value);
#            print "$atom_name 1=>$hash_value\t$species_amt[$hash_value][$k]\n";
            $species_amt[$hash_value][$k]++;          
#            print "$atom_name 2=>$hash_value\t$species_amt[$hash_value][$k]\n";
          }
        }#end else of if($j==2 or $j==3 or $j==4)
        
#      if(($j%30)==0){$_=<STDIN>;}      
      }#end else of if($i<=2)
    }#end while($line=<NEWCLST>)
  
  #output species amount at specific time duration into an individual file
  for($j=0;$j<$indx_max;$j++)
  { $z=$z_max-$j;
    printf SPC_CNT "%d\t%.2f\t",$time,$z;      #output time (ps)
    printf NM_SPC_CNT "%d\t%.2f\t",$time,$z;      #output time (ps)
    $flag_newline=1;
    for ($i=1;$i<=$size_hash;$i++)   #scan all spcies
    { 
#      if($flag_newline==1){print SPC_CNT "$z\t"};   #output slab z
      printf SPC_CNT "%.2f\t",$species_amt[$i][$j];
      printf NM_SPC_CNT "%.2f\t", $species_amt[$i][$j]/$frame_amt_per_file;
    }
    print SPC_CNT "\n";
    print NM_SPC_CNT "\n";
  }
  close(SPC_CNT); 
  close(NM_SPC_CNT); 
  }#end foreach $lmp_file (@filelist)

#### 

}#end else of if ($flag ==0)



## write commands to command file for record
my $datelog=`date`;
$datelog=tm::trim($datelog);
if ($flag == 1)
  {$flag = "successful"}
else
  {$flag = "failed"}
system("echo '$datelog  $SCRIPT_NAME status $flag' >> command");   #if running this script, write it into command for record
