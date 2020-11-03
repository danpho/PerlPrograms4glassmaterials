#!/usr/bin/perl -w
# copyright belong to Dr. Liaoyuan Wang
# this program is used to track target species(atom id based)
# Due to simulations keeping updated or continued, all target species in different time period will be first scanned and saved in an independent file "species.trk.log"
# Based on this log file, all target will be scanned and counted and saved in comp_x_xxstps_react_targetspecies.dat file
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

#   search and sort==> grep FRAME 1x200.lammpstrj.o_neighbors.raw.dat| grep -i -n La | sort -k 3 -n -u
#
#    grep 9278 1x200.lammpstrj.o_neighbors.raw.dat| sort -k 2 -n -u
#
#   add extra info ==> sed 's/^/wly /' 1x200.lammpstrj.o_neighbors.raw.dat


my $line;                   # to store line read from a file
my @values;                 # to parse each word in the $line read from a file
my $subline;
my @sub_values;             # to parse an element of values
my $L_path;                 # directory store Lanalysis
my @SPEC;                   # store target species
my @ALLSPEC;                # store all species
my $NO_FILES=25;            # number of files to scan, such as 1x200.lammpstrj.o_neighbors.raw.dat which include info for species. default value is 25 files.
my $NO_FRAME=200; 
my $DFT_ZDP='newzdp';       #All required files suppose saved in newzdp directory
my $hostname=`hostname`;    #name of host
my $DFT_SIML_STEP=1000000;  #default unit time step in each simulation

my @info_amt_spc;           #info for log. how many unique tracking species in total

my $comp;                   #compositions, machine depends
my $no_step;                #step number, machine depends
my $i_comp; my $i_no_step;  #index for comp and no_step
my $comp_path='';           #path for a composition
my @dir_simulation;         #each simulation directory, such as 500kstp, 1mstp, 1.5mstp
my $tmp_dir;               #temperary path
my $flg_dir_simulation;
my $flg_time_order=1;         #this flag is used to identify the time series is in the right order, such as 500kstp-->1mstp-->1.5mstp. If the time series is in a wrong order, it results wrong movie when tracking the reactions.
my $work_path;              #current work path
my $zdp;                    #usually use default value $DFT_ZDP,just in case
my $simulation_path='';     #$work_path/$dir_simulation[..], e.g ./500kstp; ./1mstp
my $analysis_path='';      #$simulation_path/$zdp, e.g ./500kstp/newzdp; ./1mstp/newzdp
my $no_o_nghb_files;        #file number of o_neighbors.raw.dat
my $species;                #target species
my $spcs_id;                # species+atomID
my $simulation_stp;         #default $DFT_SIML_STEP
my $file_o_nghb;            #file *.o_neighbors.raw.dat
my $file_o_nghb_refine;     #file *.o_neighbors.raw.dat, remove duplicated frame except timestep=0
my $tmp; my $sub_tmp;
my $i; my $j; my $k; my $i_SPEC;     #index for loop
my $i_stp=0;  my $i_file;   #index for control loop of steps(like 1mstp, 500kstp)  and files (like 1x200, 2x200, 3x200)
my $sn_srt;                     #serial number (used in $sub_filename,$spc_mid_srt_filename) for sorting final unique data in time series
my $sn_trk;
my $sub_filename;           #file for filtered in current directory
my $sub_react_filename;     #file for track species' reaction
my $spc_mid_filename;       #intermediate file for species
my $spc_mid_srt_filename;   #intermediate file for sorted species
my $spc_filename;           #file for filtered species
my $trk_spc_filename;       #file for tracked species
my $comp_tot_spc_filename;  #file for collecting unique atom id with the same species,such as La, Th, Ce,... file sort and filter from $comp_tot_spc_tmp
my $comp_tot_spc_tmp;           #file for collecting all atom id (may duplicate)
my $cnt_comp_spc_atomid_filename;   # count species for a fixed atomid and output the numbers into this file
my $comp_tot_trk_spc_filename;  #file for collecting unique species with the same atom id from time-series files, such 1x200.lammpstrj.o_neighbor.raw.dat
my $comp_tot_trk_spc_tmp;           #file for collecting all species with the same atom id (may duplicate)
my $comp_tot_trk_spc_his;   #His file for collecting tracked target species and the structure which the target species are in
my @spc_id;                 #species id
my @spc_name;               #species name
my @count_spc;              #count amount of species in each file, such as 1x200.lammpstrj.o_neighbors.raw.data
my $txt_count_spc;          #to control output format, convert it to three or four digit
my @sub_spc_name;           #species name for the same atom id, like 10234 O; 10234 Fe; 10234 La.....
my $flag;                   #flag for adding new species. 
my $amt_files;              #usually use default value $NO_FILE, amount of files, such as *.o_neighbors.raw.dat
my $no_fram;                #default $NO_FRAME. How many structures in a file
my $atom_id;                #atom id for sepcific species
my $name_spc;               #species names for the same atom id
my $newclst_his_filename;   #filename for *newclst.His which has structure info
my $line_no;                #store line number when search or extract section from a file, we may need to know the line number

#variables using to count species amount for a target/interested species
my @cnt_spc;                #dimensioin is same to @ALLSPEC

#variables primarily used in the module which extracts structure
my $v_head;                 #store the first timestep in a *.newclst.His
my $v_tail;                 #store the last timestep in a *.newclst.His
my $v_amt_rec;              #how many structures(timesteps) in a *.newclst.His
my $v_step;                 #step gap between each timestep.$v_step=(v_tail-v_head)/(v_amt_rec-1)
my $v_fram;                 #no of frame which consists of the specific species
#my $timestep;              #this timestep is like 500kstp, 1mstp,...
my $v_line;                 #used in visualization
my @v_values;my @v_sub_values;
my $v_tmp; my $v_i;
my $amt_species_interface;  #amount of species in interface box
my $timestep_v_fram;        #calculated timestep for grep search
my $init_line_v_fram;       #the 1st line of extracted frame
my $final_line_v_fram;      #the last line of extracted frame
my $size_file;              #size of file, like 1x200,2x200
my $sn_file;                #series number of file, like 1 in 1x200, 2 in 2x200
my $v_old_atm_id;            #store old atom id for comparison
my $v_new_atm_id;           #store new atom id for comparison
my $v_point_spc;            #pointer the target species,count how many target species searched or extracted
my $comp_spc_trk_his;       #History file for a single species. Goal to reduce file size

#$SPEC[0]="Ac";
#$SPEC[1]="Ce";
#Target species which are intersted
$SPEC[0]="La";$SPEC[1]="Ac";$SPEC[2]="Ce";$SPEC[3]="Th";
#ALL species which are labelled in History files. 
$ALLSPEC[0]="La";   #Si-OH    ==> Si-LaH
$ALLSPEC[1]="Ac";   #Al-OH  
$ALLSPEC[2]="Ce";   #Si-OH[2] 
$ALLSPEC[3]="Th";   #Al-OH[2] 
$ALLSPEC[4]="Ne";   #O-H[3]   
$ALLSPEC[5]="Ar";   #OH
$ALLSPEC[6]="Re";   #Re-X X is not hydrogen
$ALLSPEC[7]="Pr";   #Si-O[H]-Si
$ALLSPEC[8]="Yb";   #Si-O[H]-Al
$ALLSPEC[9]="Pa";   #Al-O[H]-Al
$ALLSPEC[10]="Sg";  #X-O[Z]-Y    cutoff warning, X Y are not either SI or AL
$ALLSPEC[11]="Fe";  #NBO
$ALLSPEC[12]="O";   #BO OR O IN WATER
$ALLSPEC[13]="Te";  #TBO
$ALLSPEC[14]="Se";  #Free oxygen
#$ALLSPEC[15]="SI";
#$ALLSPEC[16]="AL";
#$ALLSPEC[17]="CA";

#define a hash to make the meaning clearly
my %spc_lbl=
(
  "sioh"  => "La",
  "aloh"  => "Ac",
  "sioh2" => "Ce",
  "aloh2" => "Th",
  "h3o"   => "Ne",
  "oh"    => "Ar",
  "rex"   => "Re",
  "siohsi"=> "Pr",
  "siohal"=> "Yb",
  "alohal"=> "Pa",
  "xozy"  => "Sg",
  "NBO"   => "Fe",
  "BO"    => "O",
  "TBO"   => "Te",
  "freeo" => "Se",
);  #end hash %spc_lbl

#define a hash to save number of species
my %cnt_spc_trk;
 

## write commands to command file for record
my $datelog=`date`;
$datelog=&trim($datelog);
system("echo '$datelog  wtrack.pl' >> command");   #if running this script, write it into command for record


#identify machine
chomp($hostname);
$hostname=~s/\s+//g;
if($hostname eq "bustard")
{
  $i_comp=4;  #for composition number index in @values 
}
else
{print "Hostname is not bustard. Please check your machine name. You may need to change some parameters for your machine.\n";
}

#bustard
$L_path="/cm/shared/scripts/fortran/";
chomp($L_path);
$L_path=~s/^\s+|\s+$//g;

$work_path=`pwd`;
chomp($work_path);
$work_path=~s/^\s+|\s+$//g;
@values=split(/\//,$work_path);
$comp=$values[$i_comp];   #composition number
for($i=0;$i<=$i_comp;$i++)
{ $values[$i]=&trim($values[$i]);
  $comp_path="$comp_path"."$values[$i]/";
}
$comp_path=&trim($comp_path);

print "comp=$comp\t comp_path=$comp_path\nwork_path=$work_path\n";

@values=split(/stp/,$work_path);
@sub_values=split(/\//,$values[0]);
print colored("wtrack.pl is used to track the atomic reaction on the surface.\n The machine environment is only for bustard. If you use it in different machine, please change L_path or ask Dr. Liaoyuan Wang for help.\n","bold yellow");

#search all simulation directories
$line=`ls -d -- *stp/ |sort -n`; 
chomp($line);
@dir_simulation=split(/\s+/,$line);
#system("ls -d -- *stp/ |sort -n;");

print colored("The default timestep for simulation(not for analysis) is ","BOLD CYAN"),colored("$DFT_SIML_STEP","bold yellow"),colored(".\n Thus, 500kstp means 500,000 timestep in your simulation setting, 1mstp is $DFT_SIML_STEP timestep, and nmstp is n x $DFT_SIML_STEP timestep. If your timestep for each simulation is not ","bold cyan"),colored("$DFT_SIML_STEP","bold yellow"),colored(", please input the simulation timestep and improve setting here in the future.(ENTER for $DFT_SIML_STEP)","bold cyan");
$_=<STDIN>;
$_=&trim($_);
if(length($_) > 0){$simulation_stp=$_;}
else{$simulation_stp=$DFT_SIML_STEP;}
print "The timestep set in simulation is $simulation_stp.\n\n";

print colored("please check the sub-directory in above simulation directories to make sure ","bold cyan"),colored("*.o_neighbors.raw.dat","bold yellow"),colored(" be exisiting.\n","bold cyan");


#$tmp=$dir_simulation[0];
#$sub_tmp=$dir_simulation[$#dir_simulation];
#print"dir_simulation[0]=$dir_simulation[0]\tlength($dir_simulation[0])=",length($dir_simulation[0]),"\n";
#$_=<STDIN>;



$tmp=substr($dir_simulation[0],(length($dir_simulation[0])-5),1);
$sub_tmp=substr($dir_simulation[$#dir_simulation],(length($dir_simulation[$#dir_simulation])-5),1);

if(uc($tmp) eq "M" and uc($sub_tmp) eq "M")
{
  if($tmp le $sub_tmp)#the last value is greater than the first one
  {
    $_=pop@dir_simulation;
    unshift @dir_simulation,$_;
  }
}
elsif(uc($tmp) eq "M" and uc($sub_tmp) eq "K")
{
    $_=pop@dir_simulation;
    unshift @dir_simulation,$_;
}
else
{print colored("NOTE:","BOLD YELLOW BLINK"),"The time series is default set as ",colored("kstp","bold cyan")," or ",colored("mstp","bold cyan")," which originate from simulation directory name. If the settings of time series is wrong, the reaction series may be wrong. Please double check your simulation directories.\n";
$flg_time_order=0;
}
print "Simulation directores are below:\n",join("\n",@dir_simulation),"\n";   #list all simulation directories in seperate line

print "Input analysis directory (ENTER for $DFT_ZDP):";
$line=<STDIN>;
$line=&trim($line);
if(length($line)eq 0)
{$zdp=$DFT_ZDP;}

print "Input the amount of frames/structures in each file (ENTER for $NO_FRAME) ";
$line=<STDIN>;
$line=&trim($line);
if(length($line) >0)
{$no_fram=$line;}
else
{$no_fram=$NO_FRAME;}
 
#clean directory which may not be cleaned due to unfinished running
#if (-e .tmp or -e .react_tmp)
{system("rm -f .tmp .react_tmp");}
$comp_path="$work_path/rct_trk/"; 
print"comp_path= $comp_path\n";
if(-d $comp_path) 
{print "$comp_path is existing. Reaction files will be copied in.\n";} 
else 
{ system("mkdir $comp_path;"); 
  print "Creating $comp_path to collect reaction files.\n";
}

#choose how many files scanned
print "Input file numbers you want to scan(ENTER for $NO_FILES): ";
$line=<STDIN>;
chomp($line);
$line=~s/^\s+|\s+$//g;
if (length($line) >0)
{ $no_o_nghb_files=$line;}
else
{ $no_o_nghb_files=$NO_FILES;}

#varify the simulation directory valid, namely the required files (*.o_neighbors.raw.dat) existing and the amount of *.o_neightbors.raw.dat is same to the default one
for($i=0;$i<=$#dir_simulation;$i++)
{
  $_=&trim(`ls $dir_simulation[$i]/$DFT_ZDP/rfn*.o_neighbors.raw.dat|wc -l`);
  if ($_>0){system("rm $dir_simulation[$i]/$DFT_ZDP/rfn_*.dat");}
  $tmp=`ls $dir_simulation[$i]/$DFT_ZDP/*.o_neighbors.raw.dat|wc -l`;
  $tmp=&trim($tmp);
  @values=split(/\s+/,$tmp);
  if($tmp eq $NO_FILES)
  {print "The file amount is same to the default value $NO_FILES.\n";}
  else
  { print colored("REMINDER:","bold yellow blink")," The real file amount is not the default value $NO_FILES.\n",colored("Please double check it or you can skip this info if you know what you are doing.\n","bold yellow");
    system("echo 'ls $dir_simulation[$i]/$DFT_ZDP/*.o_neighbors.raw.dat|wc -l'; ls $dir_simulation[$i]/$DFT_ZDP/*.o_neighbors.raw.dat|wc -l; echo 'ls $dir_simulation[$i]/$DFT_ZDP/*.o_neighbors.raw.dat'; ls $dir_simulation[$i]/$DFT_ZDP/*.o_neighbors.raw.dat;");
  }#end else of if(($#values+1) eq $NO_FILES)
}#end for($i=0;$i<=$#dir_simulation;$i++)


#List species symbol
system("tail -20 $L_path/Lanalysis;");


#decide which species to be scanned. Default cannot be changed.
print "This program will scan species below. \n";
for($i=0;$i<=$#SPEC;$i++)
{print colored("$SPEC[$i]\n","bold cyan");}
print "Do you want to add more species? (ENTER for no) ";
$line=<STDIN>;
chomp($line);
$line=~s/^\s+|\s+$//g;
if(length($line) ne 0)
{ $flag=1;
  while($flag eq 1)
  {
    print "Input your interested species: ";
    $subline=<STDIN>;
    chomp($subline);
    $subline=~s/^\s+|\s+$//g;
    $tmp="$subline"."-";
    $sub_tmp=`tail -20 $L_path/Lanalysis |grep -i -n $tmp`;
    chomp($sub_tmp);
    if(length($sub_tmp)eq 0)
    {print "Input does not exist. No species added. \n";}
    else
    { 
      #search duplication
      $i=0;
      while($i<=$#SPEC)
      {
        if(uc($SPEC[$i]) eq uc($subline))
        {print "Species is existing. No any operations.\n";last;}
        else
        {$i++;}
      }#end while($i<=$#SPEC)
      if($i>$#SPEC)
      {push @SPEC,$subline;}
    }#end else of if(length($sub_tmp)eq 0)
    
    print "Do you want to continue adding interested elements(Enter for no)? ";
    $_=<STDIN>;
    chomp($_);
    $_=~s/^\s+|\s+$//g;
    if((length($_) ne 0) and (uc($_) eq 'Y' or uc($_) eq 'YES'))
    {$flag=1;}
    else
    {$flag=0;}    
  }#end while($flag eq 1)
}#end if if(length($line) ne 0)
else
{
  print"You choose not to add more species.\n";
}#end else of if(length($line) ne 0)

print "Here is the final species which will be scanned. \n";
for($i=0;$i<=$#SPEC;$i++)
{print colored("$SPEC[$i]\n","bold cyan");}

#############################################################################
#automatically run following program without any interactive communication
#
#print "Input your interested species: ";
#$species=<STDIN>;

$i_SPEC=-1; #@SPEC starts from $i_SPEC=0
while($i_SPEC<$#SPEC)
{
  $sn_srt=0;      #reset serial number when starting to scan a new species
  $i_SPEC++;
  $species=$SPEC[$i_SPEC];
  $species=&trim($species);
  
  $comp_tot_spc_filename="$comp_path/tot_$comp\_$species.dat"; 
  $comp_tot_spc_tmp="$comp_path/tot_$comp\_$species.tmp";
  $comp_tot_trk_spc_filename="$comp_path/trk_tot_$comp\_$species.dat";
  $comp_tot_trk_spc_tmp="$comp_path/trk_$comp\_$species.tmp";
  $comp_tot_trk_spc_his="$comp_path/trk_tot_$comp\_$species.His";

#print "test comp_tot_spc_filename=$comp_tot_spc_filename\n comp_tot_trk_spc_tmp=$comp_tot_trk_spc_tmp\n comp_tot_trk_spc_filename=$comp_tot_trk_spc_filename\n comp_tot_trk_spc_tmp=$comp_tot_trk_spc_tmp\n comp_tot_trk_spc_his=$comp_tot_trk_spc_his\n";
#$_=<STDIN>;

  #clean existing old files
  if(-e $comp_tot_spc_filename){system("rm $comp_tot_spc_filename");}
  if(-e $comp_tot_spc_tmp){system("rm $comp_tot_spc_tmp");}
  if(-e $comp_tot_trk_spc_filename){system("rm $comp_tot_trk_spc_filename");}
  if(-e $comp_tot_trk_spc_tmp){system("rm $comp_tot_trk_spc_tmp");}
  if(-e $comp_tot_trk_spc_his){system("rm $comp_tot_trk_spc_his");}

  if (uc($species) eq "NE")
  { 
    print "You are choosing search OH[3] which is labeled as Ne-H[3].\n";
  }
  elsif (uc($species) eq "AR")
  {
    print "You are choosing search OH which is labeled as Ar-H.\n";
  }
  elsif (uc($species) eq "RE")
  {
    print "You are choosing search O-X which is labeled as Re-X.\n";
  }
  elsif (uc($species) eq "LA")
  {
    print "You are choosing search Si-O-H which is labeled as Si-La-H.\n";
  }
  elsif (uc($species) eq "AC")
  {
    print "You are choosing search Al-O-H  ==> Al-Ac-H.\n";
  }
  elsif (uc($species) eq "CE")
  {
    print "You are choosing search Si-O-H[2]  ==> Si-Ce-H[2].\n";
  }
  elsif (uc($species) eq "TH")
  {
    print "You are choosing search Al-O-H[2]  ==> Al-Th-H[2].\n";
  }
  elsif (uc($species) eq "PR")
  {
    print "You are choosing search Si-O-HSi   ==> Si-Pr-HSi.\n";
  }
  elsif (uc($species) eq "YB")
  {
    print "You are choosing search Si-O-Al(H) ==> Si-Yb-Al(H).\n";
  }
  elsif (uc($species) eq "PA")
  {
    print "You are choosing search Al-O-HAl   ==> Al-Pa-HAl.\n";
  }
  elsif (uc($species) eq "SG")
  {
    print "You are choosing search X-O-Y(Z)   ==> X-Sg-Y(Z) cutoff warning.\n";
  }
  elsif (uc($species) eq "TA")
  {
    print "You are choosing search Ca-O-H[2]  ==> Ca-Ta-H[2].\n";
  }
  else
  {print "Your input is not correct. Quit.\n";}



###scanning species and collect their atom id in each frames of each timestep and then write them into $comp_tot_spc_filename
print colored("dir_simulation","bold red blink"),@dir_simulation,"\n";
print "zdp=$zdp\n";
print "workpath=$work_path\ncomp_path=$comp_path\n\n";#$_=<STDIN>;
  for($i_stp=0;($i_stp<=$#dir_simulation and $dir_simulation[$i_stp] ne "");$i_stp++)
  {
    #define simulation and analysis path
    $simulation_path="$work_path/$dir_simulation[$i_stp]";
    $analysis_path="$simulation_path$zdp/";
    $tmp_dir=substr($dir_simulation[$i_stp],0,length($dir_simulation[$i_stp])-1);

    $sub_filename="$analysis_path$comp\_$tmp_dir\_$species.dat";
    $sub_react_filename="$analysis_path$comp\_$tmp_dir\_react_$species.dat";
    $spc_mid_filename="$analysis_path$comp\_$tmp_dir\_$species".".mid.dat";
    $spc_mid_srt_filename="$analysis_path$comp\_$tmp_dir\_srt_$species\.mid.dat";
    $spc_filename="$analysis_path$comp\_$tmp_dir\_$species\.dat";
    $trk_spc_filename="$analysis_path$comp\_$tmp_dir\_trk_$species\.dat";
#print "sub_filename=$sub_filename\nsub_react_filename=$sub_react_filename\nspc_mid_filename=$spc_mid_filename\nspc_mid_srt_filename=$spc_mid_srt_filename\nspc_filename=$spc_filename\ntrk_spc_filename=$trk_spc_filename\n\n";
#$_=<STDIN>;
    if(($i_stp eq 0) and (-e $comp_tot_spc_filename)){system("rm $comp_tot_spc_filename ");}
    if(($i_stp eq 0) and (-e $comp_tot_spc_tmp)){system("rm $comp_tot_spc_tmp");}
    for($i_file=1;$i_file<=$no_o_nghb_files;$i_file++)
    {
      $sn_srt++;
      #if($i_stp eq 0 and $i_file eq 1) #clean old files
      if($i_file eq 1) #clean old files
      {
        if(-e $sub_filename){system("rm $sub_filename");}
        if(-e $sub_react_filename){system("rm $sub_react_filename");}
        if(-e $spc_mid_filename){system("rm $spc_mid_filename");}
        if(-e $spc_mid_srt_filename){system("rm $spc_mid_srt_filename");}
        if(-e $spc_filename){system("rm $spc_filename");}
        if(-e $trk_spc_filename){system("rm $trk_spc_filename");}
      }

      #search *o_neighbors.raw.dat file to get atom id and output to spc_mid_srt_filename
      $no_step="$i_file"."x$no_fram";
#print"test no_step=$no_step\n"; 
      $file_o_nghb="$analysis_path"."$no_step.lammpstrj.o_neighbors.raw.dat";     # like 8x200.lammpstrj.o_neighbors.raw.dat
      print "Searching ",colored("$species","bold cyan")," in $file_o_nghb\n";
#      system("grep FRAME $file_o_nghb  | grep -i -n $species |sort -k 3 -n -u  > $spc_mid_filename; ");
      system("grep FRAME $file_o_nghb  | grep -i -n $species |sort -k 3 -n -u |sed 's/^/$comp $tmp_dir $no_step $sn_srt /' >> $spc_mid_srt_filename; ");#comp_7_500kstp_srt_La.mid.dat
      system("grep FRAME $file_o_nghb  | grep -i -n $species |sort -k 3 -n -u |sed 's/^/$comp $tmp_dir $no_step $sn_srt /'  ");   #display output
#      system("sed 's/^/$comp $tmp_dir $no_step /' $spc_mid_filename >> $spc_mid_srt_filename;");
#      system("sed 's/^/$comp $no_step /' $spc_mid_filename >> $trk_spc_filename;  ");

      #remove duplicated data
      #the first frame,except for the timestep =0, in dump file
      #is the last frame in previous dump frame
      #thus, *.o_neighbors.raw.dat should remove the duplicated part
      #goal is to count number of species using *.o_neighbors.raw.dat
      #bugs existing $_=&trim(`grep -E -n 'FRAME'\$'\\s{1,}''0' $file_o_nghb | tail -1`);
      $_=&trim(`grep -E -n 'FRAME[[:space:]]*0' $file_o_nghb | tail -1`);

      @_=split(/:/,$_);
      $line_no=&trim($_[0]);  #remove the first frame if timestep is not 0
      $line_no=$line_no+1;    #frame 1
      
#print "test debug i_file loop\n";$_=<STDIN>;
    }#end for($i_file=0;$i_file<=$no_o_nghb_files;$i_file++)
    #collect target species into total species file
    system("cat $spc_mid_srt_filename >> $comp_tot_spc_tmp");     #integrate all files like comp_7_500kstp_srt_La.mid.dat to a temp file, like trk_comp_7_La.tmp
    system("sort -k 7 -n -u $comp_tot_spc_tmp |sort -k 4 -n> $comp_tot_spc_filename;");

#print "test debug i_stp loop\n";$_=<STDIN>;

  }#end for($i_stp=0;($i_stp<=$#dir_simulation and $dir_simulation[$i_stp] ne "";$i_stp++)
 
#############################################################################################
#read each atomid in $comp_tot_spc_filename from all *o_neighbor.dat files and write all data into track file
#extract structure from *.newclst.His file 
  if(not -e $comp_tot_spc_filename)
  {print colored("$comp_tot_spc_filename","bold yellow")," does NOT exist. Please rerun wtrack.pl program.\n";}
  else
  {
    print colored("\n\nStarting tracking species below.\n","bold cyan");
    system("cat $comp_tot_spc_filename");#$_=<STDIN>;

    open(TRACK,"<$comp_tot_spc_filename");#read atom id from $comp_tot_spc_filename and then scan *o_neighbor.raw.dat to get the specific id
    $sn_trk=0;            #reset serial number when starting to track a new speciesa
    $info_amt_spc[$i_SPEC]=`wc -l < $comp_tot_spc_filename`;
    $info_amt_spc[$i_SPEC]=&trim($info_amt_spc[$i_SPEC]);
    $v_point_spc=0;
    while($line=<TRACK>)
    {
      $sn_trk++;            #series number
      $v_point_spc++;       #point to current record
      $line=&trim($line);
      @values=split(/\s+/,$line);
      $atom_id=&trim($values[6]);  #Here, in $comp_tot_spc_filename,like tot_comp_7_Ac.dat, atom_id is the no. 7 value, in $comp_tot_trk_spc_filename, like trk_tot_comp_7_Ac.dat, atom_id is the no. 8 value
#print"test atom_id=$atom_id\n";
#$_=<STDIN>;
      
      #define filename for counting species with a fixed atomid
      $cnt_comp_spc_atomid_filename="$comp_path/cnt_$comp\_$species\_$atom_id.dat";
      open(CNTSPC,">$cnt_comp_spc_atomid_filename");


      if(($i_stp eq 0) and (-e $comp_tot_trk_spc_filename)){system("rm $comp_tot_trk_spc_filename ");}  #delete history tracking file

      #scan files in each simulation directory
      for($i_stp=0;($i_stp<=$#dir_simulation and $dir_simulation[$i_stp] ne "");$i_stp++)
      {
        #define simulation and analysis path
        $simulation_path="$work_path/$dir_simulation[$i_stp]";
        $analysis_path="$simulation_path$zdp/";
        $tmp_dir=substr($dir_simulation[$i_stp],0,length($dir_simulation[$i_stp])-1);

print "test520 tmp_dir=$tmp_dir\n";

        $sub_filename="$analysis_path$comp\_$tmp_dir\_$species.dat";
        $sub_react_filename="$analysis_path$comp\_$tmp_dir\_react_$species.dat";
        $spc_mid_filename="$analysis_path$comp\_$tmp_dir\_$species".".mid.dat";
        $spc_mid_srt_filename="$analysis_path$comp\_$tmp_dir\_srt_$species\.mid.dat";
        $spc_filename="$analysis_path$comp\_$tmp_dir\_$species\.dat";
        $trk_spc_filename="$analysis_path$comp\_$tmp_dir\_trk_$species\.dat";
        
        #initialize the tracking tmp file $comp_tot_trk_spc_tmp
        if(-e $comp_tot_trk_spc_tmp){system("rm $comp_tot_trk_spc_tmp;");}
        
        #search unique species in each *.o_neighbors.raw.dat
        #Although in each file, these species are unique,
        #if add them together, they may not be unique. We may see like below
        #   comp_7 500kstp 3x200 1   201   6454:FRAME     0 10854 Fe  7549SI
        #   comp_7 500kstp 4x200 1   201   6454:FRAME     0 10854 Fe  7549SI
        #   comp_7 500kstp 5x200 1   201   6454:FRAME     0 10854 Fe  7549SI
        #   comp_7 500kstp 6x200 1   201   6454:FRAME     0 10854 Fe  7549SI
        #However, it can gurantee all species are found. Another way is generate a dump.all.lammpstrj.newclst.His and dump.all.lammpstrj.o_neighbors.raw.dat
        #These two files are very big. The history file may not be handled by CrystalMaker
        for($i_file=1;$i_file<=$no_o_nghb_files;$i_file++)
        {
          $no_step="$i_file"."x$no_fram";
          $file_o_nghb="$analysis_path"."$no_step.lammpstrj.o_neighbors.raw.dat";
          $file_o_nghb_refine="$analysis_path"."rfn_$no_step.lammpstrj.o_neighbors.raw.dat";

          print "Searching ",colored("$species","bold cyan underline"),colored(" $atom_id ","bold cyan"),colored("$v_point_spc","bold magenta")," of ",colored("$info_amt_spc[$i_SPEC]","bold cyan")," in $file_o_nghb_refine\n";
          #system("grep FRAME $file_o_nghb |grep $atom_id | sort -k 3 -u | sort -k 2 |sed 's/^/$comp $tmp_dir $no_step /'>>$trk_spc_filename;"); 
          
          #output all species of a certain target atom into a temp file
          #search and count the number of species and then output these info with record in above temp file into $comp_tot_trk_spc_filename

      ### count species
      #remove duplicated info in *.o_neighbors.raw.dat
      if(($i_stp eq 0) and ($i_file eq 1))
      {
        system("cp $file_o_nghb $file_o_nghb_refine");# if timestep=0, two files are same
        #initialize the variables when change atom id at the timestep=0
        #these variables are used to count species occured during timeseries
        %cnt_spc_trk=&init_hash(%spc_lbl);
        #output header
        printf CNTSPC "%5s\t%7s\t%8s\t","comp","dir","no_step";
#        printf "%5s\t%7s\t%8s\t","comp","dir","no_step";
        for my $all_species(sort keys %spc_lbl)
        {
          printf CNTSPC "%5s\t",$spc_lbl{$all_species};
#          printf "%5s\t",$spc_lbl{$all_species};
        }      
        for my $all_species(sort keys %spc_lbl)
        {
          printf CNTSPC "accu_%6s\t",$spc_lbl{$all_species};
#          printf  "accu_%6s\t",$spc_lbl{$all_species};
        }      
        print CNTSPC "\n";
        #output the first three coloumns in the first line
#        printf CNTSPC "%5s\t%7s\t%8s\t",$comp,$tmp_dir,$no_step;
#        printf  "%5s\t%7s\t%8s\t",$comp,$tmp_dir,$no_step;
        # print CNTSPC join("\t",values %spc_lbl);
        # print CNTSPC "\taccu_",join("\taccu_",values %spc_lbl),"\n";
#        printf CNTSPC join("%5s\t",values %spc_lbl);
#        printf CNTSPC "%6s\t","accu_";
#        printf CNTSPC join("%6s\taccu_",values %spc_lbl);
#        printf CNTSPC "\n";
      }   
      else
      {system("sed -n '$line_no, \$ p' $file_o_nghb > $file_o_nghb_refine"); #remove FRAME 1 which is duplicated
      }#end else of if(($i_stp eq 0) and ($i_file eq 1))
      #count species
      printf CNTSPC "%5s\t%7s\t%8s\t",$comp,$tmp_dir,$no_step;
      for my $all_species(sort keys %spc_lbl)
      {
        #bug  $tmp=&trim(`grep -E -n 'FRAME.*$atom_id'\$'\\s{1,}''$spc_lbl{$all_species}' $file_o_nghb_refine |wc -l`);
        #$tmp=&trim(`grep -E -n 'FRAME.*$atom_id[[:space:]]*$spc_lbl{$all_species}' $file_o_nghb_refine |wc -l`);
        $tmp=&trim(`grep -E -n 'FRAME.*$atom_id\[[:space:]]*$spc_lbl{$all_species}' $file_o_nghb_refine |wc -l`);
        #print CNTSPC "\t",$tmp;
        $cnt_spc_trk{$spc_lbl{$all_species}}=$cnt_spc_trk{$spc_lbl{$all_species}}+$tmp;
        #printf CNTSPC "%5d\t%6d\n",$tmp,$cnt_spc_trk{$spc_lbl{$all_species}};
        printf CNTSPC "%5d\t",$tmp;
#        printf "%5d\t",$tmp;
#print"trk cnt $atom_id \t $all_species ==> $spc_lbl{$all_species} \t tmp=$tmp \t tot=$cnt_spc_trk{$spc_lbl{$all_species}}\n";     
      }#END for my $all_species(keys %spc_lbl)

      #print CNTSPC join("\t%6d\t",values %cnt_spc_trk);
      for my $all_species(sort keys %spc_lbl)
      {
        printf CNTSPC "%6d\t",$cnt_spc_trk{$spc_lbl{$all_species}};
#        printf  "%6d\t",$cnt_spc_trk{$spc_lbl{$all_species}};
      
      }

#      print CNTSPC "\t";
#      print CNTSPC join("\t",values %cnt_spc_trk);
      print CNTSPC "\n";
#      print  "\n";

      ### end count species


          system("grep FRAME $file_o_nghb_refine |grep $atom_id | sort -u -k 3,4 | sort -k 2 -n --stable >$comp_tot_trk_spc_tmp;");

          open(CNT,"<$comp_tot_trk_spc_tmp");
          while($subline=<CNT>)
          {
            $subline=&trim($subline);
            @sub_values=split(/\s+/,$subline);
            $sub_tmp=$sub_values[3];    #species name, like Yb, Ac, La, Fe, O, ...
            $tmp=`grep FRAME $file_o_nghb_refine |grep -i -n $atom_id | grep $sub_tmp|wc -l`;
            $tmp=&trim($tmp);
            system("grep FRAME $file_o_nghb_refine |grep -i -n $atom_id | grep $sub_tmp |sort -k 3 -u | sort -k 2 -n|sed 's/^/$comp $tmp_dir $no_step $sn_trk \t $tmp \t /'>>$comp_tot_trk_spc_filename;"); 
            system("grep FRAME $file_o_nghb_refine |grep -i -n $atom_id | grep $sub_tmp| sort -k 3 -u | sort -k 2 -n|sed 's/^/$comp $tmp_dir $no_step $sn_trk $tmp /' "); 
           
          }#end while ($subline=<CNT>)
          close(CNT);
          
        }#end for($i_file=1;$i_file<=$no_o_nghb_files;$i_file++)
        #collect tracked target species into total tracking species file
        #system("cat $comp_tot_trk_spc_tmp >> $comp_tot_trk_spc_filename");
      }#end for($i_stp=0;($i_stp<=$#dir_simulation and $dir_simulation[$i_stp] ne "");$i_stp++) 
      close(CNTSPC);
    }#end while ($line=<TRACK>)
    close(TRACK);

      #to scan and collect structure file
      #and count the amount of a species which has the same atom id
      #e.g La 9863 in 500kstp/newzdp/1x200.lampstrj.o_neighbors.raw.dat
      #same atom id, the species are O, La, Ar, Yb, Ac
      #here, when reading from $comp_tot_trk_spc_filename
      #automatically count how many species in the specific file, like 500kstp/newzdp/1x200.lampstrj.o_neighbors.raw.dat
      #also, automatically extract the structure from *.newclst.His file
      open(TRCK,"<$comp_tot_trk_spc_filename");
#print "filename ",colored("$comp_tot_trk_spc_filename\n","bold yellow");
      $v_i=0;     #count species
      $v_old_atm_id=0;
      $v_new_atm_id=0;
      $v_point_spc=0;
      while($line=<TRCK>)
      {
        $v_i++;
#print colored("$line","bold red");
        $line=&trim($line);
        @values=split(/\s+/,$line);
        $values[1]=&trim($values[1]);    #timestep
        $_=substr(trim($values[1]),(length($values[1])-4),1);    #timestep,like 500kstp/,1.5mstp/,2mstp/
        $i_stp=substr(trim($values[1]),0,length($values[1])-4);
        if(uc($_) eq "K"){$i_stp=$i_stp/1000;}  #if i_stp=500k, convert it to 0.5m
        $values[2]=&trim($values[2]);    #file number
        $i_file=&trim($values[2]);       #file number,like 1x200,3x200
        @v_values=split(/x/,$i_file);   #to get file size
        $sn_file=$v_values[0];          #1 in 1x200, 2 in 2x200,...
        $size_file=$v_values[1];        #size of file, like 200
        $values[6]=&trim($values[6]);    #frame number
        $v_fram=&trim($values[6]);       #frame number
        $atom_id=&trim($values[7]);      #atom id

        $v_tmp=&trim($values[8]);        #label for species
        #define simulation and analysis path based on info in $comp_tot_trk_spc_filename
        $simulation_path="$work_path/$values[1]/";
        $analysis_path="$simulation_path$zdp/";
#        $tmp_dir=substr($dir_simulation[$i_stp],0,length($dir_simulation[$i_stp])-1);   #such as 1x200, 2x200

        $newclst_his_filename="$analysis_path$i_file.lammpstrj.newclst.His"; 
        if($v_i eq 0)
        {
          $v_old_atm_id=$values[7];
          $v_new_atm_id=$values[7];
          $comp_spc_trk_his="$comp_path/$comp\_$species\_$atom_id.His";
        }
        $v_new_atm_id=$values[7];
        if($v_new_atm_id ne $v_old_atm_id)
        { 
          $v_old_atm_id=$v_new_atm_id;
          $v_point_spc++;
          $comp_spc_trk_his="$comp_path/$comp\_$species\_$atom_id.His";
        system("echo 'Tracking $species with $atom_id in $comp' > $comp_spc_trk_his; sed -n '2,2 p' $newclst_his_filename >> $comp_spc_trk_his;");
        }#end if($v_new_atm_id ne $v_old_atm_id)

#print colored("k/m=$_\ti_stp=$i_stp\ti_file=$i_file\tv1=$values[1]\tv2=$values[2]\tv4=$values[4]\tfram v5=$values[5]\n","bold yellow");#$_=<STDIN>;        
      ##
        #test the gap value between two timesteps to verify whether the data is complete.
        #the default value would be 100, namely, a user extract a trojectory every 100 timesteps
        #However, due to the variety of the  purpose of users' simulations, user may extract a trojectory in various step gap
        #Here,get the gap value between two timesteps

#        if($v_i eq 1)#if $v_i=1, just start tracking target species. write headers into $comp_tot_trk_spc_his 
#        {
        #system("echo 'Tracking $species of $comp' > $comp_tot_trk_spc_his; sed -n '2,2 p' $newclst_his_filename >> $comp_tot_trk_spc_his;");
#        system("echo 'Tracking $species with $atom_id in $comp' > $comp_spc_trk_his; sed -n '2,2 p' $newclst_his_filename >> $comp_spc_trk_his;");
#        }#end if($v_i eq 1)#if $v_i=1, just start tracking ....

        print "history=$newclst_his_filename\n";
        $subline=&trim(`grep timestep $newclst_his_filename|head -1`);
        @sub_values=split(/\s+/,$subline);
        $v_head=&trim($sub_values[1]);
        $subline=&trim(`grep timestep $newclst_his_filename|tail -1`);
        @sub_values=split(/\s+/,$subline);
        $v_tail=&trim($sub_values[1]);
        $v_amt_rec=&trim(`grep timestep $newclst_his_filename|wc -l`);
        $v_step=($v_tail-$v_head)/($v_amt_rec-1);   #usually is 100
#print colored("ifile=$i_file\tvhead=$v_head\tvtail=$v_tail\tv_amt_rec=$v_amt_rec\tvstep=$v_step\n","bold magenta");$_=<STDIN>;

        $timestep_v_fram=($i_stp-0.5)*$simulation_stp+($sn_file-1)*$size_file*$v_step+$v_fram*$v_step;
        $tmp="timestep";
        $sub_tmp="$timestep_v_fram";
        $_=sprintf "%-8s%10s",$tmp,$sub_tmp;

        $v_line=`grep -i -n "$_" $newclst_his_filename`;
#print colored("$_ and $v_line","bold red");$_=<STDIN>;
        @v_values=split(/\s+/,$v_line);
        $v_values[2]=&trim($v_values[2]);  #species number in a simulation timestep
        $amt_species_interface=$v_values[2];
        @v_sub_values=split(/:/,$v_values[0]);#line number for the starting segment
        $v_sub_values[0]=&trim($v_sub_values[0]);
        $init_line_v_fram=$v_sub_values[0];
        $final_line_v_fram=$init_line_v_fram+3+$amt_species_interface*2;

        print "Extracting atom ID ",colored("$atom_id","bold cyan"),", (",colored("$v_point_spc","bold magenta")," of ",colored("$info_amt_spc[$i_SPEC]","bold cyan"),"), ",colored("$v_tmp","bold magenta"),"/",colored("$species","bold cyan")," from $init_line_v_fram to $final_line_v_fram\n"; #$info_amt_spc[$i_SPEC] is the total amount of target species, $v_tmp is the labelled species name

        $v_tmp=`wc -l < $newclst_his_filename`;
        $v_tmp=&trim($v_tmp);
#        if($_ eq 1)   #if comp_tot_trk_spc_his_ has only one line, add total atom number into the 2nd line
#        {system("sed -n '2,2 p' $newclst_his_filename>>$comp_tot_trk_spc_his");}
 
        #system("sed -n '$init_line_v_fram,$final_line_v_fram p' $newclst_his_filename >> $comp_tot_trk_spc_his;");
        system("sed -n '$init_line_v_fram,$final_line_v_fram p' $newclst_his_filename >> $comp_spc_trk_his;");

      ##the atom amount in each timestep is different (because some atoms may move in or out the interface box)
         

      }#end while($line=<TRCK>) 
      close(TRCK)
  }#end else if if(not -e $comp_tot_spc_filename)
}#end while(@SPEC)

$tmp="$comp"."_$no_step"."_react_*.dat";
print "Below are the tracking files. \n",colored("$tmp","bold yellow")," can show how the species change during the time series.\n";
system("ls *react*;");
print colored("These files were copied to $comp_path. \n\n","bold MAGENTA");

$tmp="$comp"."_$no_step"."_??.dat";
print "The interested species are filetered and shown in the below files ",colored("$tmp\n","bold yellow");
system("ls $tmp");



if($flg_time_order eq 0)
{print colored("NOTE:","BOLD YELLOW BLINK"),colored("Usually the timesteps are set as ","bold cyan"),colored("kstp","bold red"),colored(" or ","bold cyan"),colored("mstp","bold red"),colored(" which originates from the simulation directories set by users. This program can automatically identify the difference. If you see this message, it means that the timestep setting may  not, at least, be like this. Please double check your timestep because this will affect the order of your species. In another word, the order of your species occured may be wrong or disordered. You need to double check this setting which is your directory name, like 500kstp, 1mstp, 1.5mstp,...\n","bold cyan");
}#end if ($flag_time_order eq 0)

###############################################################################
##subroutines

sub trim
{
  my ($subline)=@_;
  chomp($subline);
  $subline=~s/^\s+|\s+$//g;
  return $subline;
}#end sub trim


sub init_hash(\%)
{
    my (%sub_lbl)=@_;
    my %sub_cnt;
    for my $lbl(keys %spc_lbl)
    {
      $sub_cnt{$sub_lbl{$lbl}} = 0;     # e.g. AC => 0
#      print "sub '$lbl' ==> $sub_lbl{$lbl} $sub_cnt{$sub_lbl{$lbl}} \n";
    } 
    return %sub_cnt;
}   

