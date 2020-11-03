#!/usr/bin/perl -w
# Created by:			2018-08-21 16:08
# Last modified:	2018-10-23 11:02
# Filename:				wbondlength.pl
# Copyright@Liaoyuan Wang (wly_ustc@hotmail.com)
# This program is used to calculate the distance between target and neighbor atoms
# It includes cell imaging which extends all atoms in original cell to imaging cells
# calculate bond distance between target and all other atoms
# collect atoms which are in a sphere which centers at target atom and the radius is the cutoff
#set the strict condition;
#########################################
#2018-10-23 11:02 update last frame cannot be counted in
use strict;
use warnings;#give a warning message when error occured
use diagnostics; #When you do not understand the warning message, use it to learn more info.It cost a lot of resource!
use Scalar::Util qw(looks_like_number);   #used to test numeric value. OR if ($var =~ /^[+-]?/d+/$/ ){...}
use Parallel::ForkManager;
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

my $SCRIPT_NAME=$0;                             #program name
my $DFT_INPUT_STRUC_FILE="dump.all.lammpstrj";  #default structure file
my $DFT_ANL_DIR="newzdp";                       #default analystic directory
my $DFT_CUTOFF=1.507;                           #cutoff for O-H
#if it is interface box, the top of interface box may not be the top surface
#when imaging the interface box along z direction, we should consider the atoms above the interface box
#To resolve such issue, here set a flag variable
#-3:trunk interface box along z; -2 trunk interface box along y; -1: trunk interface box along x
#for -3/-2/-1, we need to consider atoms out of interface box along z/y/x
#0: no trunk, directly imaging atoms along z/y/x
my $DFT_FLG_INTERFACE=-3;             #flag control imaging box orientation and trunk
my $DFT_SEARCH_DEPTH=3;               #searching depth. 1, the first nearest neighbor; 2. 2nd nearest ones; 3. ....

my $line;                             # to store line read from a file
my $sub_line;                         # to store line when $line is used
my @values;                           # to parse each word in the $line read from a file
my @sub_values;                       # same to @values, applied it when @values is in use
my $data_line='';                        # receive returned data from a function. some variables(like $sub_string_output) consist of several info which is saved as a string
my @data_values;                      # store the splited values from $data_line
my $data_value;                       # store the value in @data_values
my $i;my $j;my $k;                    # loop index
my @final_output;                     #to reduce calculating time, save all final output into an array instead of writing to a file after analyzing each frame
our $ax_i;our $by_j;our $cz_k;        #loop index: -1,0,1

our $file_input_struc;                #input structure file, default is $DFT_INPUT_STRUC_FILE lammpstrj file
our $input;                           #read parameter
our $sn_frame=0;                      #count frame number
our $work_dir=`pwd`;chomp($work_dir); #work directory in which this program runs
our $dir_trk="rct_trk";               #directory for tracking analysis
our $sim_dir;                         #child directory which consists of *x200.lammpstrj
our $rlt_sim_dir;                     #child directory in parents,like 500kstp/newzdp,1mstp/newzdp,...
our $anly_dir=$DFT_ANL_DIR;           #analytic directory, default "newzdp"
our @dirs;                            #directories like 500kstp, 1mstp, ...
our @files;                           #files *.lammpstrj without directory
our @coord_data;                      #coordination data for target species
our @species;                         #species, like Th,Ac,La,...
our $cutoff;                          #cutoff to determine neighbor atoms 
our $cutoff_xyz=3;                    #if $flg_interface=-1/-2/-3, will extended the defined interface box along x/y/z +3A and -3A (may up to top surface which is less than 3A)
our @tgt_atm_ids;                     #all primary target atom ids
our @prmry_tgt_ngb_atm_ids;           #all neighbor atom ids of a primary target atom
our @sbsdy_tgt_ngb_atm_ids;           #all neighbor atom ids of a subsidary target atom
our $atom_id;                         #atom id
our $time_step;                       #time step
our $atm_amt;                        #all target atom amount
our $aaa;our $bbb;our $ccc;           #lattice constant


# here, define $new_aaa,$new_bbb,$new_zzz 
# use $xxx and $flg_a as an example
# we use $flg_a=+/-1 or 0 to control imaging direction, $xxx[$atom_id] is x coordination of atom $atom_id
# $xxx_ij=$xxx[$target_atom_id]-$xxx[$neighbor-atom-id]
# if the target atom locates close to boarder, it may bond with an atom in imaging cell
# $xxx_ij=$xxx_ij-$flg_a*$aaa is a universal equation
# if $flg_a==0, it is the origianl equation
# if $flg_a==-1,imaging box along -a,add   a can convert it back to original box
# if $flg_a==+1,                  +a,minus a can ...
# however, interface box may not trunk upto the maximum boarder,we cannot use periodic boundary to handle it. 
# We choose up/lo_boader+/-3A to extend the box.
# we define $new_aaa which can be set as $aaa which project the whole cell along x axis, or value $up_w+3 or $lo_g-3 which extend the boader outside 3A in case missing neighbor atoms which close to the boader and bonds to target atom but out of interface box
# NOTE: Here, if the up extended boader is beyond of the upper boader, we do not use periodic boundary to match it. This might result in a bug if the simulating system is not water+vaccuum+glass_surface

our $new_aaa;our $new_bbb;our $new_ccc;  #updated lattice constant based on $flg_interface value. if trunk box along x/y/z, then corresponding lattice constant will be boarder+/-3A instead of +/-lattice constant.eg. trunk along z, then the $up_w=
our $indx_spc_atmid;                  #index of @species and @atom_ids
our $sn;                              #data amount for each species
our $target_atom_id;                  #target atom id
our $comp_id;                         #composition ID
our $dir;                             #current working directory
our $file;                            #single file in @files without directory
our $tmp_file;                        #temporarily save each frame extracted from $file
our $output_bondlength_file;          #file saves calculated bondlength
our $spc;                             #individual target species, like La, Ne,...
our $hash_key;                        #hash key
our @xxx;our@yyy; our@zzz;            #x,y,z in original box
our @ddd;                             #multi-variables,distance between target and neighbors
our @img_ngtv_xxx;our@img_ngtv_yyy;our@img_ngtv_zzz;    #x,y,z in +a/+b/+c imaging box
our @img_pstv_xxx;our@img_pstv_yyy;our@img_pstv_zzz;    #x,y,z in -a/-b/-c imaging box
our $ddd_ij;our $xxx_ij; our $yyy_ij; our $zzz_ij;  #distance btw target and all other atoms
#our $xxx_ij_sqr;our $yyy_ij_sqr;our $zzz_ij_sqr;   #square of xxx_ij, yyy_ij, and zzz_ij
our %hash_type_spc;                   #TEST/STUDY hash to set the relations between type and spc
our %hash_spc_type;                   #TEST/STUDY hash to set the relations between type and spc
our %hash_cutoff;                     #cutoff for different atom-pairs
#my $tgt_xxx;my$tgt_yyy;my$tgt_zzz;   #x,y,z for target atom
our @atom_type;                       #read from *.lammpstrj
our @atom_chg;                        #atom charge
our @spc_type;                        #read from Lanalysis top lines before ==== end type =============
our $flg_interface;                   #default value is $DFT_FLG_INTERFACE
our @flg_intf_atm;                    #1:atom in interface box;2:atom in imaging interface box;0:out of interface and extended box
our $flg_a;my$flg_b;my$flg_c;         #flag for target atom whether it is close to corresponding boarder

#have not customized it by user
our $flg_rescan_dump=0;               #flag for rescan dump.all.lammptrj files 1: yes 0:no. 
our $flg_srch_all_nghb=0;             #flag for the second search and calculate subsidary'e neighbors. 0:search specified neighbors; 1: search all neighbors
our @nghb_name_interested;            #id of interested neighbor type/element, like H
$nghb_name_interested[0]='H';
#$nghb_name_interested[0]='SI';
#$nghb_name_interested[1]='AL';
#$nghb_name_interested[2]='H';

#sub cal_dist is used to calculate primary and subsidary target atom's neighbors based on type-pair cutoff(O-H=1.507,SI-O=2.1A)
#because one H in Al-OH2 may bond to another oxygen, therefore it is not real Al-OH2
#if the subsidary target H, which is the neighbors of primary target atom based on type-pair cutoff,also bond with another oxygen,
#the secondary scan can find it.
#Further, this substrate can be extened to for different scan depth. currently, it is limited in 2

our  $flg_primary_tgt=1;               #flag for calling sub cal_dist. if 1st call, =1; else=0
our $search_depth=$DFT_SEARCH_DEPTH;  #from the target atom as 1st depth, how many depth would be searched
our $search_i;                        #index for control of searching depth

my $up_g=-1;my$lo_g=-1;               #up: upper limit; lo:lower limit; g:glass; w:water
my $up_w=-1;my$lo_w=-1;               #up: upper limit; lo:lower limit; g:glass; w:water
my $model_file="model_info.log";      #save info for interface box and total atoms in glass and water box
my $Lanalysis="Lanalysis";            #Lanalysis file which provide type info
my $LANALYSIS="/cm/shared/scripts/fortran/Lanalysis";           #Lanalysis file which provide type info
my $tgt_spc_type;                     #type of target atom in lammpstrj file, it can be converted from the top lines in Lanalysis,like 1 Si, 2 Al, 3 Ca, 4 O, 5 H
my $tgt_spc;                          #species of target type, like O,Si,...

my $tmp;                              # to store temprary value
my $flag=1;                           # $flag=0, error occured;$flag=1, no error, program continue
my $error_msg='';                     # save error info for user debug



################################################################################
############## info for user
print colored("$0","bold cyan")," is used to calculate bond length between target and neighbors.\n";
print colored("$0 consider periodic boundary. All bond length calculated based on periodic boundary.\n","bold yellow");
print colored("Please run $0 at parents directory which consists of simulation directories, such as 500kstp, 1mstp, 1.5mstp, etc.\n","bold magenta");


################################################################################
############## collect all info


### collect simulation directories
## write commands to command file for record later
my $datelog=`date`;
$datelog=tm::trim($datelog);

#collect composition number
if($work_dir=~ /comp_/)
{
  $flag=1;
  @values=split(/comp_/,$work_dir);chomp @values;
  @sub_values=split(/\//,$values[1]);chomp @sub_values;
  $comp_id=$sub_values[0];
}#end if($work_dir=~ /comp_/)
else
{ $flag=0; $error_msg="$error_msg"."keyword comp is not available in $work_dir";
  print "current directory $work_dir does NOT consist of composition info. Please Input the composition number: ";
  $_=<STDIN>;chomp($_);
  if($_=~ /\d+/){$comp_id=$_;$error_msg="$error_msg".'';}
  else{print "Input error. Key info missed. Quit.\n";}
}#else of if($work_dir=~ /comp_/)

print colored("PLEASE CHECK SIMULATION DIRECTORIES BELOW WHICH CONSITS OF ","BOLD YELLOW"),colored("newzdp","bold magenta"),"\n";
$line=`ls |grep stp|sort -n`;chomp($line);
@values=split(/\r?\n/,$line);chomp(@values);
$input=pop(@values);
unshift(@values,"$input");
@dirs=@values;
$i=1;
foreach $dir (@dirs)
{if ($i%10 ==0){printf "%11s\n",$dir;}else{printf "%11s",$dir;}$i++;}
$i--;
print "total directory number is ",colored("$i\n","bold cyan");
print "************* END CHECK ***************\n";

print "Please check above simulation directories. Is anything wrong?(y/n ENTER for no)";
$input=<STDIN>;chomp($input);
#$input="n";
if (uc($input) eq "Y" or uc($input) eq "YES")
{$flag=0;$error_msg="$error_msg"."sim_dir invalid or file missing ";print "The name of sub-directory should consist of *stp which has directory newzdp. The simulated data must be under in newzdp   at this moment. The name of some directories may be illegal. Please rename the directory.\n";}
else
{print "No error reported. Continuing...\n";}


#name of target species
if (-d "rct_trk")
{
  #read tot_comp*.dat file to achieve names of a target species/atomId
  $line=`cat $work_dir/rct_trk/tot_comp_*.dat`;chomp($line); @values=split(/\r?\n/,$line);chomp(@values);
  $i=0;
  foreach(@values)
  {
    @sub_values=split(/\s+/,$_);chomp(@sub_values);
    $species[$i]=$sub_values[7];
    $tgt_atm_ids[$i]=$sub_values[6];
    $i++;
  }#end foreach(@values)
}#if (-d rct_trk)
else
{
  print "tot_comp_*.dat files do not exist in $work_dir/rct_trk.";
  print "Input target species: ";
  $input=<STDIN>;chomp($input);
  if($input =~ /^[a-z,.A-Z]+$/)
  {$spc=$input;}
  else
  {$flag=0;$error_msg="$error_msg;"."Input($input) illegal";print colored("$input","bold red"),colored(" should be alphabets.Quit.\n","bold yellow");}

  print "Input target atom ID: ";
  $input=<STDIN>;chomp($input);
  #if ($input=~ /^[0-9,.E,.e]+$/){$target_atom_id=$input;}
  if ($input=~ /^[0-9]$/){$target_atom_id=$input;}
  else{$flag=0;$error_msg="$error_msg;"."No numberic input (user input: $input)";print "Your input is ",colored("$input","bold red"),". ",colored("Input should be all digital numbers.Error.Quit!\n","bold yellow");}
}#end else of if (-d rct_trk)

print "Input structure file name (ENTER for default ",colored("$DFT_INPUT_STRUC_FILE","bold cyan"),") ";
$input=<STDIN>;chomp($input);$input=tm::trim($input);
if(length($input) eq 0){print "User choose default input file ",colored("$DFT_INPUT_STRUC_FILE","bold cyan"),".\n";$file_input_struc=$DFT_INPUT_STRUC_FILE;}
else
{ $file_input_struc=$input;print "The input file is $file_input_struc.\n";}

#varify $file_input_struc existing in each directory
#read info for interface box
#In general, total line number in each file should be same
#in case anything wrong, program will scan the total line number
#however, dump.all.lammpstrj is very big and such scan will cost too much time
#To save time, if these files have been scanned, the info would be save in dump.all.lammpstrj.stat
#if these files have not been scanned or there are errors, user can scan or rescan these files.
foreach $dir (@dirs)
{ 
  #define simulating directory and its subdirectory, analyzing directory for zdp analysis, named newzdp
  $sim_dir="$work_dir/$dir/$anly_dir";
  #simulated file name in each analysis directory
  $file="$sim_dir/$file_input_struc";

  #collect type info and cutoff from Lanalysis in simulation directory $Lanalysis or fortran directory $LANALYSIS
  #if data were collected, skip this step
  if(scalar @spc_type == 0)
  { 
    $Lanalysis="$sim_dir/"."$Lanalysis";
    #open (LANLYSIS,"<$Lanalysis");
    open (LANLYSIS,"<$LANALYSIS");

    ## extract type of a species and write into a hash list
    ## Here two hashs are defined
    #%hash_type_spc is used to calculate distance btw target and other atoms
    #%hash_spc_type is used to quickly find the cutoff based on cutoff setting in Lanalysis
    $i=0;
    while ($input=<LANLYSIS>)
    { $input=tm::trim($input);
      @_=split(/\s+/,$input);chomp(@_);
      if($input=~ /end type/){last;}
      elsif($i==0){$i++;next;}
      else{$spc_type[$_[0]]=$_[1];$hash_type_spc{$_[0]}=$_[1];$hash_spc_type{$_[1]}=$_[0];print"\$spc_type[$i]=$spc_type[$i]\n";}
      print "\$i=$i\t\$spc_type[$i]=$spc_type[$i]\t\$hash_spc_type{$spc_type[$i]}=$hash_spc_type{$spc_type[$i]}\t\$hash_type_spc{$i}=$hash_type_spc{$i}\n";
      $i++;
    }#end while ($input=<LANLYSIS>)


    ## extract cutoff
    #system("sed -n '/cutoff bond lengths/,/endcutoff/p' $Lanalysis > $Lanalysis.tmp");
    #open (CUTOFF,"<$Lanalysis.tmp");
    system("sed -n '/cutoff bond lengths/,/endcutoff/p' $LANALYSIS > $LANALYSIS.tmp");
    open (CUTOFF,"<$LANALYSIS.tmp");
    $i=-1;
    while($input=<CUTOFF>)
    {
      chomp($input);
      @values=split(/\s+/,$input);chomp(@values);
      if($i<1 or $input=~ /endcutoff/){$i++;next;}    #skip head two lines and the last line
      else
      {
        $hash_cutoff{"$hash_spc_type{$values[0]}"."-"."$hash_spc_type{$values[1]}"}=$values[2];
        $hash_cutoff{"$hash_spc_type{$values[1]}"."-"."$hash_spc_type{$values[0]}"}=$values[2];     #here,looks duplicated, but later when perform calculation of distance, we can directly judge bond formation using one of them 
#        print "\$hash_cutoff{$hash_spc_type{$values[0]}-$hash_spc_type{$values[1]}}=$values[2]\n";
      }

    }#end while($input=<CUTOFF>)
  }#end if(scalar @spc_type == 0)

  #check simulated file, like dump.all.lammpstrj, existing or not
  #check the total line number for each simulated files
  #here, $flg_rescan_dump==0, unconfirmed no rescan, ==1 yes confirmed rescan, ==-1 confirmed no rescan
  if(-e "dump.all.lammpstrj.stat" and $flg_rescan_dump==0)
  { system("ls -l 'dump.all.lammpstrj.stat';");#cat dump.all.lammpstrj.stat;");
    print "If you think the file info shown above may have been changed. Please answer y or yes to recollect file information.\n";
    print "Is there any problem? (y/n ENTER for no) ";
    $input=<STDIN>;$input=tm::trim($input);
    if(length($input)==0){print "No problem confirmed by user.\n";$flg_rescan_dump=-1;}
    elsif(uc($input) eq 'N' or uc($input) eq "NO"){print "No problem confirmed by user.\n";$flg_rescan_dump=-1;}
    else{ print "Error occurred. Rerun scanning.\n"; $flg_rescan_dump=1;system("rm dump.all.lammpstrj.stat");} 
  }#end if(-e "dump.all.lammpstrj.stat")
  elsif($flg_rescan_dump==-1){;}
  else
  {$flg_rescan_dump=1;}

  #if simulated files have not been scanned or user may think it is wrong
  #will rescan them
  if ($flg_rescan_dump==1)
  {
    $_=`wc -l < $file`;chomp($_); 
    open DUMP_STAT,">>dump.all.lammpstrj.stat";
    print DUMP_STAT "total line $_ in $file.\n";
  }#end if(-e "dump.all.lammpstrj.stat")
  else
  {
    $tmp=`sort -uk 3,3 dump.all.lammpstrj.stat|wc -l`;chomp($tmp);
    if($tmp eq 1){$_=`sort -uk 3,3 dump.all.lammpstrj.stat`;chomp($_);@_=split(/\s+/,$_);$_=$_[2];}
    else{print colored("Warning","bold yellow flash"),"Total line number of dump.all.lammpstrj in each directory is different. Here is the search results:  $tmp\n";$flag=0;$error_msg="$error_msg;inconsistent total line number in $file";}
  }#end else of if ($flg_rescan_dump==1)
  #if upper and lower boarder has not been assigned,
  #will read model_info.log file to read them
  if(-e $file){print colored("$file_input_struc ($_ lines) exists in $sim_dir.\n","bold cyan");}
  else{print colored("$file_input_struc does NOT exist in $sim_dir.\n","bold red");$flag=0;$error_msg="$error_msg;$file_input_struc missed in $sim_dir";}
  if ($up_g==-1 or $up_w==-1 or $lo_g==-1 or $lo_w==-1)
  {
    if(-e "$sim_dir/$model_file")
    {
      $line=`tail -3 $sim_dir/$model_file |head -2`;    #extract info for up_g,lo_g,up_w,and lo_w
      @values=split(/\r|\n/,$line);chomp(@values);
      for(my $ss=0;$ss<=$#values;$ss++)                 #remove spaces in each line
      { $values[$ss]=tm::trim($values[$ss]);
        @_=split(/\s+/,$values[$ss]);
        if($ss==0){$up_g=$_[1];$lo_g=$_[3];}
        else{$up_w=$_[1];$lo_w=$_[3];}
      }
    }#end if(-e $sim_dir/$model_file)
  }#end if ($up_g==-1 or $up_w==-1 or $lo_g==-1 or $lo_w==-1)
}#end foreach $dir (@dirs) 

print colored("Please check above file size which should be same or very close each other.\n","bold yellow");
print "Is there anything wrong?(y/n, ENTER for no) ";
$input=<STDIN>;$input=tm::trim($input);
if(length($input) == 0){print "\nNo error reported. Continue.\n";}
elsif(uc($input) eq "Y" or uc($input) eq "YES"){$flag=0;$error_msg="$error_msg;user report size of $file_input_struc error";print "\nUser reported size of $file_input_struc does NOT match each other. Quit.\n";}
elsif(uc($input) eq "N" or uc($input) eq "NO"){print "\nUser confirmed no errors.\n";}
else{print "\nInvalid input. Choose defualt no error occured. Continuing. \n";}

print "Input trunking orientation (x/y/z,ENTER for default z orientation) ";
$input=<STDIN>;$input=tm::trim($input);
if(length($input) == 0){print "User choose to trunk along z orientation.\n";$flg_interface=-3;}
elsif(uc($input) eq 'Z'){print "User choose to trunk along z orientation.\n";$flg_interface=-3;}
elsif(uc($input) eq 'Y'){print "User choose to trunk along y orientation.\n";$flg_interface=-2;}
elsif(uc($input) eq 'X'){print "User choose to trunk along x orientation.\n";$flg_interface=-1;}
else{print "User choose to extend the imaging box along x,y,z. CTRL+C or CTRL+Z to cancel this program.\n";$flg_interface=0;} 

#input of target atom id will be improved in automatic or manual ways
#neighbor id will be improved in the future
print "Input target atom ID: ";
$input=<STDIN>;chomp $input;$input=tm::trim($input);$_=$input;
#if(length($input) eq 0 or $input =~ s/\D//g){$flag=0;print "Invalid atom ID($_). Quit.\n";$error_msg="$error_msg"."Invalid atom ID: $_";}
if(length($input) eq 0 or $input =~ s/\D//g){$flag=0;print "Invalid atom ID($_). Quit.\n";$error_msg="$error_msg"."Invalid atom ID: $_";}
else{$target_atom_id=$input;print "Input target atom ID:",colored("$target_atom_id","bold cyan"),".\n";}

####cutoff setting to determine neighbors
###print "Input cutoff value (ENTER for default $DFT_CUTOFF A): ";
###$input=<STDIN>;chomp($input);$_=$input;
####if ($input=~ /^[0-9,.E,.e]+$/){$cutoff=$input;}
###if (length($input) == 0){$cutoff=$DFT_CUTOFF;}
###elsif($input=~ /\d/){$cutoff=$input;}
###else{$flag=0;$error_msg="$error_msg;"."No numberic input (user input: $input)";print "Your input is ",colored("$input","bold red"),". ",colored("Input should be all digital numbers.Error.Quit!\n","bold yellow");}

foreach $input (keys (%hash_cutoff))
{printf "cutoff between types:%5s ==> %.3f A\n",$input,$hash_cutoff{$input};}

##################################################################################################
#################  MAIN ##################
if($flag == 1)
{
  my $total_line;
  my @line_no;
  my $first_line_frm;my$last_line_frm;          #first and last line # of each frame
################################################################################
############## read lammpstrj and convert coordinates
  print "Counting frame number and line number. Please wait ...\n";
  $sn_frame=0;chomp@line_no;


  #output file name
  #$output_bondlength_file="$work_dir/$dir_trk/$hash_type_spc{$atom_type[$target_atom_id]}_$target_atom_id\_bondlength.dat";
  $output_bondlength_file="$work_dir/$dir_trk/$target_atom_id\_bondlength.dat";

  if(-e $output_bondlength_file){tm::rename($output_bondlength_file);}#if file exist, rename it based on current time

  open(OUTPUT,">$output_bondlength_file");

  #each line the data set may be varied, here, only give title rule
  print OUTPUT "FrameNO\tTitle Rule: LabelOfTargetType(PRMRYTGT or SBSDRYTGT)\tTargetAtomID\tTargetAtomName\tNeighborAtomID\tNeighborAtomName\tBondLenght\tNeighborAtomID\t...\n";
  print  "FrameNO\tLabel\tPrimaryTargetID\tPrimaryTargetName\tNeighborAtomID\tNeighborAtomName\tBondLength ...\n";

  foreach $dir (@dirs)
  {
    #simulation dir,like 500kstp,1mstp,1.5mstp,...
    #analysistic dir,like newzdp
    $sim_dir="$work_dir/$dir/$anly_dir";
    $rlt_sim_dir="./$dir/$anly_dir";
    $file="$sim_dir/$file_input_struc";
    $total_line=`wc -l < $file`;chomp $total_line;
 
 
    #read the first line of each frame
    $line=`grep -n TIMESTEP $file`;chomp($line);
    @values=split(/\r|\n/,$line);chomp(@values);
    $i=0;
    #reset @line_no
    $#line_no=-1;

    #########################################################################################
    #### Here, there are three loops
    #### 1st loop is used to read line # of each frame in raw data file,*.lammpstrj,
    #### 2nd loop is used to collect atomic data, such as coordinates, type, name, flags (for in interface box, trunk along which axis[x/y/z]) in one frame
    #### 3rd loop is used to calculate the distance btw target and the 1st nearest neighbor atoms
    ####  a). 3rd loop will be run in a function
    ####  b). 3rd loop will also calculate the distance between the 1st and the 2nd nearest neighbor atoms
    ####    to calculate the distance btw 1st and 2nd nearest neighbors, the distance btw target and the 1st nearest neighbors will be calculated first
    ######################################################################################### 


    #########################
    #### 1st loop: get line # of each frame in raw data file *.lammpstrj
    # assign line no of the first line of each frame to @line_no 
    foreach $input(@values)
    { 
      @sub_values=split(/:/,$input);chomp(@sub_values);
      $line_no[$i]=$sub_values[0];
      $i++;
    }#end foreach $input(@values)
 
    ##the last frame will not be counted if the simulating directory is not the last one owing to the last frame being the same to the first frame in the    following directory
    ## However, if it is the last directory, the last frame should be counted. 
    ## To resolve such issue, here, add last_line_no+1 to @line_no, so the rest of this script does not need to change
    if($dir eq $dirs[$#dirs])
    {$tmp=`wc -l $file`;chomp($tmp);$tmp=$tmp+1;push(@line_no,$tmp);} #$tmp is the last line # of $file, $tmp+1 is to match $last_line_frm=$line_no[$k]-1
    else{;}

 
    #########################
    #### 2nd loop: collect atomic data, such as coordinates, type, name, flags (for in interface box, trunk along which axis[x/y/ z]) in one frame
    #in each dump.all.lammpstrj file, except the first file with TIMESTEP starting from 0,
    #the rest of these files have duplicated time step
    #e.g. in the dump.all.lammptrj in 500kstp, the last time step is 500000
    #in the dump.all.lammpstrj in 1mstp, the first time step is 500000
    #we need remove such duplications
    #All line number in each file has been recorded in @line_no
    #We can control the loop index to read it or not based on file location (500kstp, 1mstp,...)
    for ($j=0;$j<$#line_no;$j++)  #to extract one frame, the last frame is intentionally skipped because it is the same to the first frame except for timestep=0
    {
      $k=$j+1;    #to get the first line number of next frame
      $first_line_frm=$line_no[$j];
      $last_line_frm=$line_no[$k]-1;          #last line no for the target frame
      $tmp_file="$file.tmp";
      print "Extracting frame sn: $sn_frame\tindex: $j\t1st_line: $line_no[$j]\tlast_line: $last_line_frm\n";
      #system("sed -n '$line_no[$j], $last_line_frm p' $file >$tmp_file;cat $tmp_file;");
      system("sed -n \"$first_line_frm, $last_line_frm p\" $file >$tmp_file;");#cat $tmp_file;");
      ###read all data in one frame
      open(TMP_FILE,"<$tmp_file");
      $i=0;                       #use count line # in each frame saved in *.lammptrj.tmp
      $search_i=0;                #use to control searching depth
      while ($line=<TMP_FILE>)
      {
        $i++; 
        chomp($line);$line=tm::trim($line);
        @values=split(/\s+/,$line);chomp@values;
        if($i==1 or $i==3 or $i==5 or $i==9){next;}   #skip ITEM:...
        elsif($i==2){$time_step=$line;}                                #TIMESTEP
        elsif($i==4){$atm_amt=$line;}
        elsif($i==6){$aaa=$values[1]-$values[0];}
        elsif($i==7){$bbb=$values[1]-$values[0];}
        elsif($i==8){$ccc=$values[1]-$values[0];}
        else
        {#convert fractional coordinates to absolute coordinates
          $atom_id=$values[0];
          $atom_type[$atom_id]=$values[1];            #type
          $atom_chg[$atom_id]=$values[2];             #charge
          $xxx[$atom_id]=$aaa*$values[3];             #coordinator x
          $yyy[$atom_id]=$bbb*$values[4];             #coordinator y
          $zzz[$atom_id]=$ccc*$values[5];             #coordinator z

          #$flg_intf_atm: flag atoms in inteface box and extended box in different flag
          #0:out of extended box;
          #1:in interface box;
          #2:in extended box but out of interface box
          if($flg_interface<0)
          { 
            if($flg_interface==-3)              #extend along z direction
            {
              $new_aaa=$aaa;$new_bbb=$bbb;$new_ccc=0;   #a,b direction will be duplicated periodically, boader along c will be extended
              #mark atom in the interface box, extended box, and out of extended box
              if($zzz[$atom_id] <= $up_w and $zzz[$atom_id] >= $lo_g){$flg_intf_atm[$atom_id]=1;}
              elsif(($zzz[$atom_id] <= ($up_w+$cutoff_xyz) and $zzz[$atom_id] > $up_w) or ($zzz[$atom_id] <$lo_g and $zzz[$atom_id] >=($lo_g-$cutoff_xyz))){$flg_intf_atm[$atom_id]=2;}
              else{$flg_intf_atm[$atom_id]=0;}
  
            }#end if($flg_interface==-3) 
            elsif($flg_interface==-2)           #extend along y direction
            {
              $new_aaa=$aaa;$new_bbb=0;$new_ccc=$ccc;   #a,c direction will be duplicated periodically, boader along b will be extended
              #mark atom in the interface box, extended box, and out of extended box
              if($yyy[$atom_id] <= $up_w and $yyy[$atom_id] >= $lo_g){$flg_intf_atm[$atom_id]=1;}
              elsif(($yyy[$atom_id] <= ($up_w+$cutoff_xyz) and $yyy[$atom_id] > $up_w) or ($yyy[$atom_id] <$lo_g and $yyy[$atom_id] >=($lo_g-$cutoff_xyz))){$flg_intf_atm[$atom_id]=2;}
              else{$flg_intf_atm[$atom_id]=0;}
  
            }#end elsif($flg_interface==-2)
            else                                #extend along x direction
            {
              $new_aaa=0;$new_bbb=$bbb;$new_ccc=$ccc;   #b,c direction will be duplicated periodically, boader along a will be extended
              #mark atom in the interface box, extended box, and out of extended box
              if($xxx[$atom_id] <= $up_w and $xxx[$atom_id] >= $lo_g){$flg_intf_atm[$atom_id]=1;}
              elsif(($xxx[$atom_id] <= ($up_w+$cutoff_xyz) and $xxx[$atom_id] > $up_w) or ($xxx[$atom_id] <$lo_g and $xxx[$atom_id] >=($lo_g-$cutoff_xyz))){$flg_intf_atm[$atom_id]=2;}
              else{$flg_intf_atm[$atom_id]=0;}

            }#end else of elsif($flg_interface==-2)
          }#end if($flg_interface<0)
          elsif($flg_interface==0)
          {
            ####NOTE here, $up_w and $lo_g are the upper and bottom boader, namely $up_w-$lo_g=$aaa or $bbb or $ccc
            $new_aaa=$aaa;$new_bbb=$bbb;$new_ccc=$ccc;   #cell along a,b,c direction will be duplicated periodically
            #mark atom in the interface box, extended box, and out of extended box
            if($yyy[$atom_id] <= $up_w and $yyy[$atom_id] >= $lo_g){$flg_intf_atm[$atom_id]=1;}
            else{$flg_intf_atm[$atom_id]=0;}
 
          }#end elsif($flg_interface==0)
          else  #nothing to do
          {;}
        }#end else of elsif.... of if($i==1 or $i==3 or $i==5 or $i==9)
      }#end while ($line=<TMP_FILE>)

      ## determine location of target atom whether it is close to boarder or not
      ## to save calculating time
      # -1: extend interface box -a/b/c; +1: extend interface box +a/b/c; 0: no extention
      if($xxx[$target_atom_id]<=3){$flg_a=-1;}
      elsif(($xxx[$target_atom_id]+3)>=$aaa){$flg_a=1;}
      else{$flg_a=0;}

      if($yyy[$target_atom_id]<=3){$flg_b=-1;}
      elsif(($yyy[$target_atom_id]+3)>=$bbb){$flg_b=1;}
      else{$flg_b=0;}

      if($zzz[$target_atom_id]<=3){$flg_c=-1;}
      elsif(($zzz[$target_atom_id]+3)>=$ccc){$flg_c=1;}
      else{$flg_c=0;}


      #above finish reading one frame, converting fractional coordinates to absolute values, flagging atoms which are in the interface box
      #and extended box, flagging primary target atom (here is oxygen) which is the species we are interested in, flagging the secondary target
      #(here is hydrogen) which is the neighbor of the primary target atom but it may bond to other atoms
      #Below is calculating bond length between target atoms and atoms in interface and extended box
      #s1:        check "neighbor" atom is in the interface box
      #s1.1:      if no, go to next atom
      #s1.2:      if yes, check it is close to the boundary
      #s1.2.1:    if yes consider atoms in the interface box or imaging box
      #s1.2.2:    if no (not close to the boundary), directly calculate the distance using coordinates in the interface box, 
      #s1.2.1/2.1:  check the charge polarity of target and "neighbor" atom whether different
      #s1.2.1/2.2:  if yes, calculate the distance, else go to next atom
      #s1.2.1/2.3:  output the bondlength and atom id, atom type/name
      #
      #foreach $target_atom_id (@target_atoms)
      print "Calculating distance between target(",colored("$target_atom_id","bold cyan"),") and atoms in interface or extended or imaging box in c",colored("$comp_id","bold cyan")," frame # ",colored("$sn_frame","bold magenta")," @ $rlt_sim_dir .\n"; 
      #empty @prmry_tgt_ngb_atm_ids
      @prmry_tgt_ngb_atm_ids=();      

      #@prmry_tgt_ngb_atm_ids=&cal_dist($target_atom_id);chomp@prmry_tgt_ngb_atm_ids;
      $data_line=&cal_dist($target_atom_id);$data_line=tm::trim($data_line);         #here use $data_line to temporarily store return string
      @data_values=split(/\s+/,$data_line);chomp @data_values;

      #scan the second order neighbors,e.g. H bonded to H if Al-Th-H-O exist
      $i=0; 
      foreach $data_value (@data_values)
      {
        #@data_values consists of target_atom_id, neighbor_atom_i_id, distance_i,....
        #1. read neighbor id as subsidary target atom id
        #2. based on setting decide to search neighbors of all/specified subsidary atom and calculate corresponding bond length
        #3. output all data to file
        if($i%3!=1 or $data_value=~ /TGT/){$i++;next;}          #skip target atom id and bond length
        else  #$data_value is neighbor atom id of target atom here
        {
          $i++;
          if ($flg_srch_all_nghb == 0)        #only search specified elements
          {
            foreach $input (@nghb_name_interested)
            {
              $_=$atom_type[$data_value];chomp($_);
              #if ($hash_type_spc{$atom_type[$data_value]} eq $input)       #subsidary target atom is the interested atom
              if ($hash_type_spc{$_} eq $input)       #subsidary target atom is the interested atom
              {
                $_=&cal_dist($data_value);        #input subsidary atom id of a target atom and get its neighbors and bond length
                $data_line="$data_line\t$_";      #joint the 1st and 2nd order neighbors together
              }
            }#end foreach $input (@nghb_name_interested) 
          }#end if ($flg_srch_all_nghb == 0)
          else                                #scan all elements
          {
            
          }#end else of if ($flg_srch_all_nghb == 0) 
        }#end else of if($i%2==0)

        #output
      }#end foreach (@data_values)
       
      #output results to a file 
      #print colored("$data_line \n","bold magenta");
      print OUTPUT "$data_line\n";
      if($sn_frame%20 !=0 or $sn_frame==0)
      {$final_output[$sn_frame]=$data_line;}
      else{print colored("test quit.\n","bold yellow");exit;}


      #here, index changes, and all coordinates will be displayed because the coordinates have been calculated/converted
      $sn_frame++;
    }#end for my $j=0;$j<$#line_no;$j++;
    
  
  }#foreach $dir (@dirs)

  for($i=0;$i<$sn_frame;$i++)
  {print OUTPUT "$final_output[$i]\n";}

################################################################################
#read target atom and corresponding neighbors


################################################################################
#calculate imaging neighbor atoms


################################################################################
#calculate bond length between target atom and imaging neighbors



system("echo '$datelog  $SCRIPT_NAME STATUS: $flag' >> command");   #if running this script, write it into command for record
}#end if($flag==1)
else
{  
  system("echo '$datelog  $SCRIPT_NAME STATUS: $flag. ERROR MSG:$error_msg ' >> command");   #if running this script, write it into command for record
  print "Error Occured. Please check command to read the details.\n";system("tail -1 command");
}


################################################################################
############## subroutine or function
#calculate distance between two atoms and return bond length between target and neighbor atoms
sub cal_dist      #$target_atom_id,$atom_id,target_atom_charge,atom_charge,target_x,target_y,target_z,atom_x,atom_y,atom_z,cutoff
{
#  my ($sub_tgt_atm_id,$sub_atm_id,$sub_tgt_chrg,$sub_atm_chrg,$sub_tgt_xxx,$sub_tgt_yyy,$sub_tgy_zzz,$sub_atm_xxx,$sub_atm_yyy,$sub_atm_zzz,$sub_cutoff)=@_;
#  my ($sub_tgt_atm_id,$sub_atm_id)=@_;
#  my ($sub_tgt_atm_id,$sub_flg_primary_tgt)=@_;chomp ($sub_tgt_atm_id,$sub_flg_primary_tgt);
  my ($sub_tgt_atm_id)=@_;chomp ($sub_tgt_atm_id);
  my $sub_i;my $sub_j;my $sub_k;        #index for x,y, and z
  my $sub_atm_id;                       #atom id using in subroutine                    
  my @sub_subsdry_tgt_atm_id;           #neighbors of the subsidary target atom 
  my $sub_id_indx=0;                    #index for array @sub_subsdry_tgt_atm_id
  my @sub_ddd;                          #collect all bondlength for primary and subsidary target atom in one line
  my $sub_string_output;                #all data save in one string variable
  
  #PERL does not support return an array. Here, collect all data together and write into a string variable
  #In main program, it can be parsed.
  #set sign to tell primary target atom and subsidary atom
  if($sub_tgt_atm_id eq $target_atom_id)
  {$sub_string_output=sprintf("%15d  %8s  %8d  %5s",$sn_frame,'PRMRYTGT',$sub_tgt_atm_id,$hash_type_spc{$atom_type[$sub_tgt_atm_id]});}
  else
  {$sub_string_output=sprintf("%8s  %8d  %5s",'SBSDRYTGT',$sub_tgt_atm_id,$hash_type_spc{$atom_type[$sub_tgt_atm_id]});}

  #Subroutine is used to calculate distance between target and atoms in interface and extended box
  #s1:        check "neighbor" atom is in the interface box
  #s1.1:      if no, go to next atom
  #s1.2:      if yes, check it is close to the boundary
  #s1.2.1:    if yes consider atoms in the interface box or imaging box
  #s1.2.2:    if no (not close to the boundary), directly calculate the distance using coordinates in the interface box, 
  #s1.2.1/2.1:  check the charge polarity of target and "neighbor" atom whether different
  #s1.2.1/2.2:  if yes, calculate the distance, else go to next atom
  #s1.2.1/2.3:  output the bondlength and atom id, atom type/name
  #
  #foreach $target_atom_id (@target_atoms)

#  print "Sub calculating distance between target(",colored("$sub_tgt_atm_id","bold cyan"),") and atoms in interface or extended or imaging box in $rlt_sim_dir.\n";
  $atom_type[$sub_tgt_atm_id]=tm::trim($atom_type[$sub_tgt_atm_id]);
######test speedup  printf "%5s %8d %.3f %.3f %.3f\n",$hash_type_spc{$atom_type[$sub_tgt_atm_id]},$sub_tgt_atm_id,$xxx[$sub_tgt_atm_id],$yyy[$sub_tgt_atm_id],$zzz[$sub_tgt_atm_id];

  #calculate distance between target atom and the rest of all other atoms
  #Here, to save calculating time, only those target atoms close to the boundary are considered to calculate the atoms in the neighbor CELL
  #No matter whether the target atom is close to boarder or not, the calculation between two atoms in the interface box will be performed
  #it is in default $flg_a,$flg_b,$flg_c=0

  #for($sub_atm_id=1;$sub_atm_id<=$#flg_intf_atm;$sub_atm_id++)
  for($sub_atm_id=$#flg_intf_atm;$sub_atm_id>=1;$sub_atm_id--)
  {  
    if($sub_atm_id==$sub_tgt_atm_id or $atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]>0 or $flg_intf_atm[$sub_atm_id]==0){next;}   #exclude target atom self or make sure two atoms have different polarity or atoms out of interface/extended box
    else
    {
      $xxx_ij=$xxx[$sub_tgt_atm_id]-$xxx[$sub_atm_id]; 
      $yyy_ij=$yyy[$sub_tgt_atm_id]-$yyy[$sub_atm_id]; 
      $zzz_ij=$zzz[$sub_tgt_atm_id]-$zzz[$sub_atm_id]; 
      
      #only consider target atom bond with atoms in imaging box
      for($sub_i=0;$sub_i<=abs($flg_a);$sub_i++)
      { 
       
        for($sub_j=0;$sub_j<=abs($flg_b);$sub_j++)
        {
    
          for($sub_k=0;$sub_k<=abs($flg_c);$sub_k++)
          {

            if($atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]<0)   #different charge polarity
            {
              #$ddd[$target_atom_id][$sub_atm_id][$ax_i][$by_j][$cz_k][$sub_id_indx]=sqrt(($xxx_ij-$flg_a*$new_aaa)**2+($yyy_ij-$flg_b*$new_bbb)**2+($zzz_ij-$flg_c*$new_ccc)**2);
              $ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]=sqrt(($xxx_ij-$flg_a*$new_aaa)**2+($yyy_ij-$flg_b*$new_bbb)**2+($zzz_ij-$flg_c*$new_ccc)**2);
              $hash_key="$atom_type[$sub_tgt_atm_id]"."-"."$atom_type[$sub_atm_id]";

              if($ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx] <= $hash_cutoff{$hash_key})
              {
                #printf OUTPUT "%6d\t%4s\t%6d\t%4s\t%6d\t%.3f\t%4d\t%4d\t%4d\t%.3f\n",$sn_frame,                                     $hash_type_spc{$atom_type[$target_atom_id]},$target_atom_id,$hash_type_spc{$atom_type[$sub_atm_id]},$sub_atm_id,$hash_cutoff{$hash_key},$flg_a,$flg_b,$flg_c,$ddd[$target_atom_id][$sub_atm_id][$ax_i][$by_j][$cz_k][$sub_id_indx];

                $sub_ddd[$sub_id_indx]=$ddd[$target_atom_id][$sub_atm_id][$sub_id_indx];

                chomp ($sub_tgt_atm_id,$target_atom_id);
                if($sub_atm_id ne $target_atom_id)
                {
                  #$_=sprintf("%8d\t%5s\t%.3f",$sub_atm_id,$hash_type_spc{$atom_type[$sub_atm_id]},$ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]);
                  $_=sprintf("%8d  %5s  %.3f",$sub_atm_id,$hash_type_spc{$atom_type[$sub_atm_id]},$ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]);
                  chomp ($_,$sub_string_output);
                  $sub_string_output="$sub_string_output  $_";
                }


#$sub_string_output="$sub_string_output\t$sn_frame\t$hash_type_spc{$atom_type[$target_atom_id]}\t$target_atom_id\t$hash_type_spc{$atom_type[$sub_atm_id]}\t$sub_atm_id\t$ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]";
###test speedup                printf "%6d\t%4s\t%6d\t%4s\t%6d\t%.3f\t%4d\t%4d\t%4d\t%.3f\n",$sn_frame,                                     $hash_type_spc{$atom_type[$target_atom_id]},$sub_tgt_atm_id,$hash_type_spc{$atom_type[$sub_atm_id]},$sub_atm_id,$hash_cutoff{$hash_key},$flg_a,$flg_b,$flg_c,$ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx];


              }#end if($ddd[$target_atom_id][$sub_atm_id][$ax_i][$by_j][$cz_k][$sub_id_indx] <= $hash_cutoff{$hash_key})

            }#end if($atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]<0)

          }#end for($sub_k=0;$sub_k<=abs($flg_c);$sub_k++)
        }#end for($sub_j=0;$sub_j<=abs($flg_b);$sub_j++)
      }#end for($sub_i=0;$sub_i<=abs($flg_a);$sub_i++)


    }#end else if($sub_atm_id==$sub_tgt_atm_id or $atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]>0 or $flg_intf_atm[$sub_atm_id]==0)

  }#end for($sub_atm_id=1;$sub_atm_id<=$#flg_intf_atm;$sub_atm_id++)

  #PERL does not support return arrays. Therefore, neighbor id and associated bondlength cannot be return in two arrays
  #To resolve this issue, here joint all data (target_id, neighbor_id, neighbor_distance) in a fixed format "primary_target_id, neighbor1_id, neighbor1_bondlength,....)
  #In addition, if the subsidary target atom does not have other neighbors except for target atom, the return value should be empty.
  $sub_string_output=tm::trim($sub_string_output);
  @_=split(/\s+/,$sub_string_output);chomp(@_);
#print colored("$sub_string_output\n","bold yellow");
#$_="SBSDRYTGT";
  if (scalar(@_) ==3 and $sub_string_output=~ m/SBSDRYTGT/){$sub_string_output='';}
#print "return:",colored("$sub_string_output\n","bold yellow");
#$_=<STDIN>;

  ($sub_string_output);       #return all neighbor id and associated bond length in one line
}#end sub cal_dist
