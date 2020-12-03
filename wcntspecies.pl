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
# Created by:2017-05-14 22:17
# Last modified:	2018-04-05 16:47
#
# Filename:		wcntspecies.pl
#
# Description:
#
#=====================================================*/
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
#    print "\n"; \n";

use tm;       #tm::trim(...)

my $PROGRAM_NAME="wcntspecies.pl";
my $line;     # to store line read from a file
my @values;   # to parse each word in the $line read from a file

#print colored("$PROGRAM_NAME","BOLD CYAN")," is used to count how many species in time series.\n";
my $FILENAME='newclst.His';chomp($FILENAME);
my $FRAMES=200;             #200 frames/file
my $FILE_AMT=25;
my @ELEMENTS;
my $CONTROL_FILE="xhst.dat";  #control file in which it consists of important parameters
my $unit_timestep=0.25;     #unit fs, here should be ?x200, namely there are 201 frames in each file. NOTE: simulation time step is 0.25fs, but LAMMPS extract one frame every 100 timesteps, and each simulation consists of 5000 frames, one file covers 5000x100x0.25=125000fs=125ps=0.125ns

$ELEMENTS[1]='Ne';$ELEMENTS[2]='Ar';$ELEMENTS[3]='Re';$ELEMENTS[4]='La';$ELEMENTS[5]='Ac';$ELEMENTS[6]='Ce';
$ELEMENTS[7]='Th';$ELEMENTS[8]='Pr';$ELEMENTS[9]='Yb';$ELEMENTS[10]='Pa';$ELEMENTS[11]='Sg';$ELEMENTS[12]='Fe';
$ELEMENTS[13]='Te';$ELEMENTS[14]='Se';$ELEMENTS[15]='O';$ELEMENTS[16]='H';

my $flag=1;   #if any error occured, quit program
if (-e "$CONTROL_FILE"){$flag=1;}
else{$flag=0;}

if($flag!=1)
{print colored("Warning","bold yellow blink"),": ",colored("$CONTROL_FILE","bold red")," does NOT exist! Quit!\n";}
else
{
  my $lmp_file=`sed -n '7,7 p' $CONTROL_FILE`; $lmp_file=tm::trim($lmp_file); #get input file name
  my $time_stamp=`sed -n '14,14 p' $CONTROL_FILE`;$time_stamp=tm::trim($time_stamp); #get timestep label, like 500kstp, 10mstp
  my $mycomp=`sed -n '15,15 p' $CONTROL_FILE`;$mycomp=tm::trim($mycomp);
  my $total_depth=`sed -n '16,16 p' $CONTROL_FILE`;$total_depth=tm::trim($total_depth);
  
  #print"wcntspecies.pl lmp_file=$lmp_file\t";
  my $filename;
  my $newclst_his_files;    #use asterisk(*) to define all target files
  my $timestep;
  my $time_real;
  my $z_up;
  my $z_lo;
  my $dr;
  my $program_parents;  #which program call this program, read from xhst.dat. currently parent programs are wslab.pl and wzdpdumpg2l.pl
  my $i;my $j;        #loop index
  my $amt_file;       #amount of files
  my $amt_frames;     #amount of frames
  my @amt_species;    #amount of sepcies
  my $spc_slb_distr_filename;   #if this program is called by wslab.pl, file consists of species distribution in different slabs but fixed time, like slb_1x200.lammpstrj.species.statistic.dat; if called by wzdpdumpl2g.pl, file name would be like 1x200.lammpstrj.species.statistic.dat
  my @filelist;       #list for all .newclst.His files
  my $tmp;            #tempory variable
  
  #### there are two program (wslab.pl and wzdpdumpl2g.pl) calling this program. 
  # to identify which one call this program, xhst.dat provide parent program at the 17th line
  # thus the parent program needs to be confirmed first.
  $_=`wc -l < $CONTROL_FILE`;
  chomp($_);
  if($_ eq 17 or $_==17)
  {$program_parents=`sed -n '17,17 p' $CONTROL_FILE`;chomp($program_parents);}
  else
  {print colored("Warning","bold yellow blink"),": $CONTROL_FILE only has $_ lines(suppose 17 lines). It may not include the info of parent procedure which call this program.\nPlease double check $CONTROL_FILE. CTRL+Z or CTRL+C to quit.\n";}
  
  #to get all input files like z_*_*x200.lammpstrj.newclst.His
  if(uc($program_parents) eq "WSLAB.PL")
  { $newclst_his_files="z_*_$lmp_file.newclst.His";
    #to get interface box range and dr
    #in xhst.dat, depth in water and glass box are positive or negative due to they are using different origin and direction
    #here, suppose water box is above glass box
    $_=`sed -n '5,5 p' $CONTROL_FILE`;chomp($_);
    $tmp=`sed -n '6,6 p' $CONTROL_FILE`;chomp($tmp);
    $dr=abs(abs($_)-abs($tmp)); 
    $spc_slb_distr_filename="slb_$lmp_file.species.statistic.dat";
  }
  elsif(uc($program_parents) eq "WZDPDUMPL2G.PL")
  { $newclst_his_files="$lmp_file.newclst.His";
    $dr=0;
    $spc_slb_distr_filename="$lmp_file.species.statistic.dat";
  }
  else
  {print "Unknown parent procedure. Please specify it at the 16th line in $CONTROL_FILE. You may see errors below. Please use CTRL+Z or CTRL+c to stop this program and rerun it after specifying parent procedure in $CONTROL_FILE.\n";}
  
  #clean files
  if(-e $spc_slb_distr_filename){system("ls $spc_slb_distr_filename;rm $spc_slb_distr_filename;");}
  
  #$line=`ls -lv $newclst_his_files |cut -d " " -f 10`;#sometimes the space between each column is more than one
  $line=`ls $newclst_his_files |sort -n`;
  @filelist=split(/\r?\n/,$line);
  
  #$amt_file=`ls z_*_$lmp_file.newclst.His |wc -l`;
  $amt_file=`ls $newclst_his_files  |wc -l`;
  $amt_file=tm::trim($amt_file);
  $amt_frames=$FRAMES;
  
  #to get timestamp and real time
  #to get timestamp
  if(lc($time_stamp)=~ /kstp/)
  { @_=split(/kstp/,lc($time_stamp));chomp(@_);
    if($_[0] le 0){$timestep=0;}
    else{$timestep=($_[0]-500)*1000*$unit_timestep/1e3;} #ps 0-125ps
  }#end if(lc($time_stamp)=~ /kstp/)
  elsif(lc($time_stamp)=~ /mstp/)
  { @_=split(/mstp/,lc($time_stamp));
    if(tm::trim($_[0]) eq 0){$timestep=0;}
    else{$timestep=($_[0]-0.5)*1e6*$unit_timestep/1e3;} #ps 
  }#end elsif(lc($time_stamp)=~ /mstp/)
  else
  {print colored("Unknown timestep label. Please ask programer.\n","bold yellow");$timestep="NA";}
  
  #duplicated operation. it is the $lmp_file showwn in above
  @_=split(/x/,$lmp_file);chomp(@_);
  @values=split(/\./,$_[1]);chomp($values[0]);
  
  if($values[0] eq $FRAMES)
  {$time_real=$_[0]*$values[0]*$unit_timestep*100/1e3;}    #here,200 denotes 200 frames,100 denotes 100 timesteps
  else
  { print colored("Warning","bold yellow blink"),"real time information is not available.Real time is set to be",colored("0","bold red blink"),". Please contact Dr. Liaoyuan Wang to improve the code.\n";
    $time_real=0;
  }#end else of if($values[0] eq 200)
  
  $time_real=$time_real+$timestep;
  
  #print"$_ x $values[0] x $unit_timestep x 100/1000=$time_real\n";
  #print"wcntspecies.pl timestep=$timestep\ttime_real=$time_real\n";
  #$_=<STDIN>;
  
  
  open(CNT,">$spc_slb_distr_filename");
  #write title into file
  $_=`wc -l < $spc_slb_distr_filename`;chomp($_);
  if($_<1)  #if file existing, not output title
  { #print CNT "tstp(ps)\tz(top->btm)\t";
    print CNT "tstp(ps)\tz(A)\t";
    for ($j=1;$j<=$#ELEMENTS;$j++)  #title
    { 
      chomp($ELEMENTS[$j]);
      if($j<$#ELEMENTS){printf CNT "%-6s ",$ELEMENTS[$j];}
      else{print CNT "$ELEMENTS[$j]\n";}
    }#end for ($j=1;$j<=$#ELEMENTS;$j++) #title
  }#end if(not -e $spc_slb_distr_filename)
  
  #output the header to $lmp_file  

  #count species number and write into $spc_slb_distr_filename
  $i=0;
  foreach $filename (@filelist)
  {
    $i++;
    #in wslab.pl, xhst.dat was kept updating until the maximum glass depth achieved
    #to find the range of interface box, the glass depth, Zg_up,Zw_lo,and total_depth 
    if($i==1)
    {
      $_=`sed -n '5,5 p' $CONTROL_FILE`;chomp($_);       #maximum depth of glass
      $tmp=`sed -n '9,9 p' $CONTROL_FILE`;chomp($tmp);   #top surface of glass
      $z_lo=$tmp-$_;                                #bottom of interface box
      $z_up=$z_lo+$total_depth;                     #top of interface box
    }
    else
    { $z_up=$z_up-$dr;}                             #top of slab
    
    print "Counting file ",$filename,"\n";
    printf CNT "%-8s\t%3d\t",$time_real,$z_up;      #real time,z step
    for($j=1;$j<=$#ELEMENTS;$j++)          #
     {
       $amt_species[$i][$j]=`grep "$ELEMENTS[$j]" $filename | wc -l`;
       chomp($amt_species[$i][$j]);
      #print "$ELEMENTS[$j]  $amt_species[$i][$j]\n";
       if($j<$#ELEMENTS){printf CNT "%-6d ",$amt_species[$i][$j];printf "%-6d ",$amt_species[$i][$j];}
       else{printf CNT "%-6d\n",$amt_species[$i][$j];printf "%-6d\n",$amt_species[$i][$j];}
     }
#    if(lc($program_parents) eq "wzdpdumpl2g.pl")    #integrate all data into one file
#    { if($i==1){system("cat $spc_slb_distr_filename > $mycomp\_$time_stamp\_spc.statistics.dat;");} #include header and data
#      else{system("tail -1 $spc_slb_distr_filename >> $mycomp\_$time_stamp\_spc.statistics.dat;");} #only data
#    }
 
  }#end foreach $filename (@filelist)
  
  system("echo '';echo 'cat $spc_slb_distr_filename';pwd;cat $spc_slb_distr_filename;");
  close(CNT);
}#end else of if($flag!=1)


my $datelog=`date`;
$datelog=tm::trim($datelog);
system("echo '$datelog $PROGRAM_NAME STATUS $flag' >> command");
