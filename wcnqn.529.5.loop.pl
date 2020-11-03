#!/usr/bin/perl -w
# Created by:			2018-08-21 16:08
# Last modified:	2019-03-30 00:01
# Filename:		wcnqn.auto.pl
# Copyright@Liaoyuan Wang (wly_ustc@hotmail.com)
# v2019-03-07-15-55
# NOTE:
# All users MUST CHECK default settings below. If you have any questions, olease contact Dr. Wang through above email
# You also need to check the control files
#
# This program is used to analyze coordination number and Qn distribution
# It calculates the distance between target and neighbor atoms
# It includes cell imaging which extends all atoms in original cell to imaging cells
# calculate bond distance between target and all other atoms
# collect atoms which are in a sphere which centers at target atom and the radius is the cutoff
# calculate 1st level neighbors of target atom and then determine CN
# calculate 2nd level neighbors of target atom and then determine Qn
#set the strict condition;
#########################################
##2018-10-23 10:48 update last frame cannot be counted in
##2018-11-21 01:00 calculate and search target neighbors and collect corresponding bond info at specified search depth, default value can be checked at default settings
##2018-11-24 11:56 atoms close to the boarder have logic error. program keeps running but no output
##2018-11-24 23:10    bug fixed.search flag was set improperly. if no neighbor atoms, it should be false or 0
##2018-11-26 11:16 output of some species shows duplicated output neighbors, such as O17006 in c9
##2018-11-26 20:36    if target atom is close to the boarder, it may be calculated multiple times because the imaging box will be counted in. Add @          sub_exclude_atm_ids to remove redundant calculation in sub cal_dist
##2018-11-25 12:21 add function to calculate CN and Qn distribution based on selected samples, you can choose all trojectories as a sample, but it takes for a long while
##2018-11-30 05:11 change $sn_frame from serial number to real number using $sn_time_step/$dump_gap. So displayed info is more clear; add real time 
##2018-12-04 09:06 add function to calculate CN, and output CN to *bondlength.dat. So user can know the former/oxygen CN, other species would be given [-1]
##2018-12-05 16:40 if one atom have one more neighbors, only one neighbor is scanned.
##2018-12-07 13:47    improper flag setting in main program if($search_level >= $search_depth or scalar(@sbsdy_tgt_ngb_atm_ids) ==0) and improper control in sub NextTarget
##                    if(scalar(@sbsdy_tgt_ngb_atm_ids) ==0)
##2018-12-07 17:21 the CN for the 1st level neighbor is wrong
##2018-12-09 09:05    delete an improper if control "if($sub_atm_id ne $target_atom_id)",however, this will results in duplicate data for target atom
##2018-12-10 07:23 output format looks massy
##2018-12-10 21:23    add if control 
##2018-12-11 17:09 add qn distribution in this program (now only for one species)
##2018-12-19 10:11 bug found for Qn analysis. Qn of Al7236 becomes to 2 at frame 21900 (5475fs). This value should be 3
##                 frame 163200 (40800fs) Qn=0 which should be 3
##                 frame 171600 (42900fs) Qn=-1 which should be 3
##2018-12-22 16:13    fixed. improved control condition if(grep(/$tgt_nm/,@former_lists) and uc($ngb_nm) eq 'O' and $cn_no <=1 and $search_level == 1) instead of if(grep(/$tgt_nm/,@former_lists)). Here $search_level must be 1 denoting neighbor oxygens directly bond to target atom
##2018-12-23 13:05 target atom is in the extended box! Program still runs. This is unacceptable. If target atom is close to the boarder of extended box, the neighbors might be missed
##2018-12-23 20:12    fixed.add BD as a label. 
##                 display the neighbors improperly. 
##2018-12-26 11:57    fixed displaying issue. There is an if control filter those target atoms
##                    if(grep /$sub_atm_id/, @sub_exclude_atm_ids){;}       #if neighbor atom is in exclude list, do nothing because it has been calculated
##                    else{$sub_string_output="$sub_string_output\t$_";}
##2018-12-31 08:49 add a control when user wants to suspend job at some point. Currently, when program starts to analyze data in new simulating directory, it will check such file "STOP" at parent directory which hold all simulating directories, if it exists, program will write regarding information into this file for record.
##2019-01-12 15:23 CN/Qn distribution can be successfully analyzed. For future use, more information is provided. 
##                  1. CN/Qn distribution of formers,modifers, and oxygen in interface box only
##                  2. CN/Qn distribution of formers,modifers, and oxygen in extended box. In which, the distribution might not be complete
##                  3. sampling size can be randomly set
##                  4. For user convenience, user can set sample based on time, program will automatically convert it into timestep
##                  5. if user modify model_info.dat, the thickness of interface box can be set into different value ==> layer/slab CN/Qn distribution can be analyzed
##2019-01-15 10:21  6. output those former's atom ID if CN != Qn
##                  7. output absolute CN/Qn and average CN/Qn
##                  8. improve info in log file
##2019-01-28 17:01  9. output all formers' CN and Qn in the interface box for further analysis as well as CN==Qn.
##2019-02-17 01:05  10.When read LAMMPS control file, if there is notation symbol '#', this line will be skipped.However, there is no error info if there is notation in command line of LAMMPS control file. Added info into $error_msg so use can know what is going wrong 
##2019-02-28 10:26  11.CN distribution of formers is need to specify into each former.
##2019-02-28 17:38    fixed this issue. defined %hash_former_indv_CN_cnt, %hash_former_indv_Qn_cnt, %hash_former_exbox_indv_CN_cnt and %hash_former_exbox_indv_Qn_cnt
##2019-03-01 15:56  12.CN distribution cannot be compared to each other. <== Normalization
##                    based on xhst.f, avg CN distribution has been normalized by species amount in the target box
##                    e.g. [4]Si/tot_Si_interfacebox
##2019-03-03 09:24  13. oxygen in water or glass has not been identified
##                    add four variables:$oxy_gls_intf_cnt, $oxy_gls_exbox_cnt, $oxy_wtr_intf_cnt, and $oxy_wtr_exbox_cnt.
##                    reorganized the output. for average output, for total, tot/samp_size, for specific species, cnt_spc/tot_spc
##2019-03-07 15:55  14. fixed tiny bugs. tested bulk CN and Qn.
##2019-03-14 10:50  15. CN/Qn distribution shows some data unusual when bulk is considered. After checking the output, it looks the upper boundary is set improperly. <-- change $up_w = $ccc or $ccc= $up_w. Here, there is a problem. How to decide the upper bondary? If the z of top atom is chosen, it may result in too close interatom distance when periodic boundary along z is considered. If not, how to set it?
##                    test 1: set $ccc=$up_w=$zzz[top atom], add switch in this program.
##2019-03-17 23:53    add $ctrl_flg_exist_vacuum and $flg_vacuum variables.
##                    $ctrl_flg_exist_vacuum='UV' or 'NV' or 'IV' ==> $flg_vacuum= 1,0,-1 respectively
##                    set $lo_g=$cutoff_xyz instead of 0 if vacuum exists in the upper or bottom box along z direction, same for x,y 
##                    so surface analysis can be reused for bulk analysis
##                    this may make the CN/Qn values less than true values,however the errors can be avoided
##                    for bulk without vacuum or vacuum in the middle of box somewhere like a sandwich, no impulse
##2019-03-27 23:47 add notes regarding extended box
##                    in main program, flag all atoms as 0, 1, 2 which denotes out of interface+extended box, in the interface box
##                    and in the extended box, respectively
##                    in subroutine cal_dist,skipping atoms with $flg_intf_atm[$sub_atm_id]==0 can speed up the analysis
##                    however, we have to consider those atoms close boarders which may bond to those atoms acrossing the boarder
##                    If it happened, the skipped atom will not bond to the target atom 
##                    therefore, a extended box was defined and atoms in it are flagged, 
##                    defined atoms in extended box are still using for bondlength calculation
##                    only atoms in the interface and extended box are used to calculate the bondlength
##                 NOTE: OUTPUT regarding extended is ONLY for reference, these atoms are not in the interface box
##2019-04-12 11:41 ??need to add labelling function which can tell which species is formed in PRMRYTGT line, ??add time calculation function??
##2019-05-28 21:44 wlabel.pl can accomplish below functions. In the future, the core program will be integrated into this program.
##                 the algorithm in wlabel.pl needs to be improved to speed up. 
##                 Concurrent technique may be applied into this program. 
##                    1. add labelling function
##                      1.1 need to tell hydrogen bond or not
##                        1.1.1 hydrogen bond between primary target O and H 
##                        1.1.2 hydrogen bond between H in primary line and another oxygen
##                      1.2 identify species, SiOH, SiOH2, AlOH, AlOH2, OH, H3O, .....
##                    2. ?? add time calculation function to calcuate species lifetime
##2019-06-06 16:25 improve CN/Qn analysis. Allow user output CN/Qn distribution for all atoms in the interface box
##                  so user can track CN/Qn as a function of time
##                  $SCRIPT_VERSION="v2019-06-06-16-25";
##2019-06-06       update version and keep the version record in this notes
##version: see $SCRIPT_VERSION below
use strict;
use warnings;#give a warning message when error occured
use diagnostics; #When you do not understand the warning message, use it to learn more info.It cost a lot of resource!
use Scalar::Util qw(looks_like_number);   #used to test numeric value. OR if ($var =~ /^[+-]?/d+/$/ ){...}
use List::Util qw[min max];             #used to compare two numeric values
#use Parallel::ForkManager;
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
use tm;     #module for clean variables. tm::trim(...), written by Liaoyuan Wang
use rc;     #module for read value which may include default one. rc::read_custmz(<info for user(string)>,<value>), written by Liaoyuan Wang
######################################################## default settings ##############################################################
#user should check these default settings in case unknown errors or incompatible settings
#these settings source from LAMMPS in_file and user customized settings, like Lanalysis, 0analysis
#all Perl programs written by Liaoyuan Wang are preferred to use Lanalysis to set cutoff, species name corresponding to type,..
#for more details please see example Lanalysis which is developped from 0analysis
#many settings may various. In this case, programs always ask user to confirm
#this program is automatically wrong without interactive mode. So all program with *.auto.pl can be submitted to computing node
#For all new users, please run regular program without *.pl first to double check your settings and understand the settings in auto one. 
#This is very important and necessary.
########################################################################################################################################
open (DEBUG,">coordinate.dat");

VARIABLES:
my $SCRIPT_NAME=$0;                             #program name
#my $SCRIPT_VERSION="v2019-03-07-15-55";
my $SCRIPT_VERSION="v2019-06-06-16-25";

#default value from LAMMPS in_file
#del#my $DFT_TIME_STEP=0.25;                         #unit fs/step. Please check your LAMMPS setting file
#del#my $DFT_DUMP_GAP=100;                           #every 100 timesteps dump one trojectory
#my @DFT_FORMER_LISTS;                           #default formers
#$DFT_FORMER_LISTS[0]='SI';
#$DFT_FORMER_LISTS[1]='AL';
#my @DFT_MODIFIER_LISTS;                         #default modifiers
#$DFT_MODIFIER_LISTS[0]='CA';

our %former_cnt;                                  #count former amount of an oxygen

#if it is interface box, the top of interface box may not be the top surface
#when imaging the interface box along z direction, we should consider the atoms above the interface box
#To resolve such issue, here set a flag variable
#-3:trunk interface box along z; -2 trunk interface box along y; -1: trunk interface box along x
#for -3/-2/-1, we need to consider atoms out of interface box along z/y/x
#0: no trunk, directly imaging atoms along z/y/x

#del# my $DFT_FLG_INTERFACE=-3;             #flag control imaging box orientation and trunk direction. -3:z,-2:y,-1:x
#del# my $DFT_SEARCH_DEPTH=1;               #searching depth. 1, the first nearest neighbor; 2. 2nd nearest ones; 3. ....
my $line;                             # to store line read from a file
my $sub_line;                         # to store line when $line is used
my @values;                           # to parse each word in the $line read from a file
my @sub_values;                       # same to @values, applied it when @values is in use
my $data_line='';                     # receive returned data from a function. some variables(like $sub_string_output) consist of several info which is saved as a string
#my @data_values;                      # store the splited values from $data_line
my $data_value;                       # store the value in @data_values
my $i;my $j;my $k;                    # loop index
my @final_output;                     # to speed up, save all data into an array.
my $time_step;                        # timestep from LAMMPS in_file
my $dump_gap;                         # dump gap between each trojectory from LAMMPS in_file
my $size_frame;                       # frame size (how many lines in each frame) If this value is not integer, the file is incomplete.
#my $ax_i;my $by_j;my $cz_k;          #loop index: -1,0,1

my  $input;                           #read parameter
my  $sn_frame;                        #count frame number
my  $work_dir=`pwd`;chomp($work_dir); #work directory in which this program runs
my  $sim_dir;                         #child directory which consists of *x200.lammpstrj
my  $file_input_struc;                #input structure file,like dump.all.lammpstrj 
my  $file_cn_qn;                      #file for CN/Qn distribution
my  $file_former_cn_EQ_qn;            #file for former atom id if CN==Qn
my  $file_former_cn_NE_qn;            #file for former atom id if CN!=Qn
my  $file_former_id_cn_qn;            #file for all former atom id
my  $file_modifier_id_cn;
my  $file_oxygen_id_cn;
my  $file_hydrogen_id_cn;
my  $file_all_spc_cn;
my  $rlt_sim_dir;                     #child directory in parents,like 500kstp/newzdp,1mstp/newzdp,...
our @dirs;                            #directories like 500kstp, 1mstp, ...
our @files;                           #files *.lammpstrj without directory
our @coord_data;                      #coordination data for target species
our @species;                         #species, like Th,Ac,La,...
our $max_cutoff=0;                    #cutoff to determine neighbor atoms
our $cutoff_xyz=3;                    #if $flg_interface=-1/-2/-3, will extended the defined interface box along x/y/z +3A and -3A (may up to top surface which is less than 3A)
our @tgt_atm_ids;                     #all primary target atom ids
our @prmry_tgt_ngb_atm_ids;           #all neighbor atom ids of a primary target atom
our @sbsdy_tgt_ngb_atm_ids;           #all neighbor atom ids of a subsidary target atom
our @exclude_atm_ids;                 #exclude atm ids which are parent target atom ids to avoid duplicated calculation
our @tmp_ngb_atm_ids;                 #tempororily save neighbor atom ids which will be assigned to @sbsdy_tgt_ngb_atm_ids
our $size_exclude_atm_ids;            #save size of exclude_atm_ids. if it is changed, search move to further level;or skip searching process to save time
our $atom_id;                         #atom id
my  $search_atom_id;                  #save atom id for those target id which will be searched
my  $search_nghb_id;                  # search neighbor's atom id
our $sn_time_step;                    # serial number of time_step which shown below TIMESTEP in trojectory file which is different from $time_step (0.25fs default)
my  $frm_time;                        #convert timestep to real time.=$sn_time_step*$time_step
our $atm_amt;                        #all target atom amount
our $aaa;our $bbb;our $ccc;           #lattice constant

my $ctrl_flg_command_tgt_id;          #which command(BL/CN) will be excuted based on the given number.>0, BL; <=0 CN & Qnnd_tgt_id
my $ctrl_flg_exist_vacuum;           #flag to show whether there is existing vacuum in the structure,allowed value:0(no),1(yes,vacuum locates in the top or bottom of structure);may use -1 to show vaccum in the middle of structure
my $ctrl_flg_varify_data;             #flag for varify data files. Y: verified; N: non-varified/need to reverify
my $ctrl_flg_search_all_nghb;         #flag for searching all/interested neighbor atoms A:all, I:interested
my $ctrl_formers;                     #formers listed in one line
my $ctrl_modifers;                    #modifers listed in one line
my $ctrl_sim_dir_keyword;             #keyword in simulating directory, like .../500kstp/
my $ctrl_anly_dir;                    #analyzing dirctory name in simulating directory, like "newzdp" in.../500kstp/newzdp/, here is "newzdp"
my $ctrl_dump_struc_file;             #dump file name
my $ctrl_dir_trck;                    #tracking directory name
my $ctrl_comp_keyword;                #common keyword for compositions, like comp_1, comp_2.....
my $ctrl_Lanalysis;                   #control file for zdp, bat, and His/DLpoly file
my $ctrl_model_info_file;             #model_info.log which consists of total atom number, glass and water atom number, thickness of interface box
my $ctrl_orientation_trunk;           #axis of surface cut perpendiculared to. 
my $ctrl_search_depth;                #sedarch depth
my $ctrl_lammps_in_file;              #LAMMPS in file
my $ctrl_starting_time_sampling;      #for CN/Qn distribution, will be converted into frame number
my $ctrl_ending_time_sampling;        #for CN/Qn distribution, will be converted into frame number
my $ctrl_loop_tstp_sampling;          #loop step, used for loop control of $ctrl_starting_time_sampling and $ctrl_ending_time_sampling. only for CN/Qn analysis with limited frames, other analysis use default value=0
my $ctrl_loop_max_time_sampling;      #maximum time for loop control above $ctrl_loop_tstp_sampling
my $ctrl_max_cn;                      #maximum CN between all species, such as formers, modifers, oxygen,...
my @sampling_t_lists;                 #save set time when performing CN/Qn analysis for limited frames
my $sampling_t_loop_i;                #loop index for @sampling_t_lists
my $amt_frame;                        #count how many frames in a sample to calculate average CN and Qn
my $flg_vacuum;                       #convert $ctrl_flg_exist_vacuum from abbr. to -1,0,1 which represents IV,NV,and UV, respectively
my $flg_BL;                           #switch variable. 1: BL; 0: CN/Qn

### there are many different layer structures, like one solid layer, one solid layer with one vacuum, two solid layers with an interface but no vacuum, two solid layers with an interface and vacuum in the bottom or upper box, two solid layers with a vacuum between them but no vacuum in the upper and bottom box, ....
### these different arrangements make the program complicated and too long
### to reuse existing codes and make the program clear and simple,
### all input parameters should be unchangeable and set some new variables which like switches
### variables used in functional modules should be completely independent to the input parameters
### when some condition is activated, run regrading modules
#my $upper_threshold_z;                #upper threshold for z axis
#my $upper_threshold_y;                #upper threshold for y axis
my $upper_threshold;                  #upper threshold of a defined box
my $lower_threshold;                  #lower threshold of a defined box
#my $lower_threshold_y;                #lower threshold for y axis
#my $lower_threshold_x;                #lower threshold for x axis

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
# NOTE: Here, if the up extended boader is beyond of the upper boader, we do not use periodic boundary to match it. This might result in a bug if the simulating system is not water+vacuum+glass_surface

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
our @flg_intf_atm;                    #1:atom in interface box;2:atom in imaging interface box;0:out of interface and extended bontf_atmx
my  $atm_nm;                          #atom name
my  $cnt_atm_tot_intf=0;              #count atom amount in interface box
my  $cnt_atm_tot_exbox=0;             #count atom amount in extended box
my  $cnt_former_intf=0;               #count former in the interface box
my  $cnt_former_exbox=0;              #count former in the extended box
my  $cnt_oxyg_intf=0;
my  $oxy_gls_intf_cnt=0;
my  $oxy_wtr_intf_cnt=0;
my  $cnt_oxyg_exbox=0;
my  $oxy_gls_exbox_cnt=0;
my  $oxy_wtr_exbox_cnt=0;
my  $cnt_modf_intf=0;
my  $cnt_modf_exbox=0;
my  $cnt_hydg_intf=0;
my  $cnt_hydg_exbox=0;
my  $cnt_other_intf=0;
my  $cnt_other_exbox=0;
my  @amt_atm_intf;                    # atom amount in interface box
my  @amt_atm_exbox;                   # atom amount in extended box
my @atm_ids;                          #save atom ids for loop
my $flg_a;my$flg_b;my$flg_c;          #flag for target atom whether it is close to corresponding boarder
my $flg_search;                       #control search level/depth working with $search_depth

#to search neighbors at different level, using flag is a better way which allow us to search different levels based on demands
our @flg_neighbor_level;              #flag all neighbor atoms based on search level.e.g. 1: first neighbor directly bond to target atom, 2: second neighbors bond to 1st neighbors,..... 

#variables customized it by user
our $flg_rescan_dump=0;               #flag for rescan dump.all.lammptrj files 1: yes 0:no. 
our $flg_srch_all_nghb=1;             #flag for the second search and calculate subsidary'e neighbors. 0:search specified neighbors; 1: search all neighbors
our @nghb_name_interested;            #id of interested neighbor type/element, like H
$nghb_name_interested[0]='H';
$nghb_name_interested[1]='O';
#$nghb_name_interested[2]='SI';
#$nghb_name_interested[3]='AL';
#$nghb_name_interested[4]='CA';

#sub cal_dist is used to calculate primary and subsidary target atom's neighbors based on type-pair cutoff(O-H=1.507,SI-O=2.1A)
#because one H in Al-OH2 may bond to another oxygen, therefore it is not real Al-OH2
#if the subsidary target H, which is the neighbors of primary target atom based on type-pair cutoff,also bond with another oxygen,
#the secondary scan can find it.
#Further, this substrate can be extened to for different scan depth. currently, it is limited in 2

our  $flg_primary_tgt=1;              #flag for calling sub cal_dist. if 1st call, =1; else=0
my  $search_depth;                    #from the target atom as 1st depth, how many depth would be searched. User should set in input_control.in. However, for CN, =1
my  $search_level;                    #search level for an individual atom
our $search_i;                        #index for control of searching depth

my $up_g=-1;my$lo_g=-1;               #up: upper limit; lo:lower limit; g:glass; w:water
my $up_w=-1;my$lo_w=-1;               #up: upper limit; lo:lower limit; g:glass; w:water
my $atm_amt_tot;                      #total atom amount in the model
my $atm_amt_glass;                    #total/maximum atom amount in glass. used to tell oxygen in glass or water
my $atm_amt_water;                    #total/maximum atom amount in water. used to tell oxygen in glass or water
my $Lanalysis="Lanalysis";            #Lanalysis file which provide type info
my $LANALYSIS="/cm/shared/scripts/fortran/Lanalysis";           #Lanalysis file which provide type info
my $input_control_file="input_control.in";     #time duration for extracting samples. eg. 0-50 fs ~ 0-200frames if timestep=0.25fs and extract one frame every 100 timesteps.

my $tmp;                              # to store temprary value
my $flag=1;                           # $flag=0, error occured;$flag=1, no error, program continue
my $error_msg='';                     # save error info for user debug
my $warn_msg='';                      # something may be wrong. keep this message for user to check

#variables for CN and Qn distribution
our @former_lists;                    #former lists
our @modifer_lists;                   #modifier lists
#our @ngh_atm_ids;                     #collect all neighbor atom IDs of a target atom
#our @tgt_neighbor_atm_ids;                     #collect all neighbor atom IDs of a target atom

my $timestep_min;                       #minimum timestep, used to set the lower limit
my $time_min;                           #minimum setting time. unit: fs
my $timestep_max;                       #maximum timestep, used to set the upper limit
my $time_max;                           #maximum setting time. unit: fs 
my $time_gap;                           #time gap between two sequential frames or timesteps shown in dump file
my $cn_no;                              #save CN for current species
my $tgt_cn;                             #cn of target atom
my $tgt_qn;                             #qn of target atom
my $tgt_nm;                             #target name
my $dft_qn;                             #default qn would be the former's CN 
my $ngb_nm;                             #neighbor name
#here define variables to count total amount of CN or Qn
#for sepcific species, the variables will be defined after reading species list, like former list
my %hash_former_cn_tot_amt;             #total amount of each CN for formers in interface box.$flg_intf_atm==1
my %hash_former_intf_indv_amt;          # amount for each individual formers in interface box.$flg_intf_atm==1
my %hash_former_exbox_cn_tot_amt;       #total amount of each CN for formers in extended box. $flg_intf_atm==2
my %hash_former_exbox_indv_amt;         # amount for each individual formers in extended box. $flg_intf_atm==2
my %hash_former_qn_tot_amt;             #total Qn for formers in interface box.$flg_intf_atm==1
my %hash_former_exbox_qn_tot_amt;       #total Qn for formers in extended box.$flg_intf_atm==2
my %hash_oxygen_cn_tot_amt;             #total CN for oxygen  in interface box.$flg_intf_atm==1
my %hash_oxygen_cn_exbox_tot_amt;       #total CN for oxygen  in interface box.$flg_intf_atm==2
my %hash_oxygen_cn_glass_tot_amt;       #total CN for oxygen  in glass locates in interface box.$flg_intf_atm==1
my %hash_oxygen_cn_glass_exbox_tot_amt; #total CN for oxygen  in glass locates in extended box.$flg_intf_atm==1
my %hash_oxygen_cn_water_tot_amt;       #total CN for oxygen  in water locates in interface box.$flg_intf_atm==2
my %hash_oxygen_cn_water_exbox_tot_amt; #total CN for oxygen  in water locates in extended box.$flg_intf_atm==2
my %hash_modifier_cn_tot_amt;           #total CN for calcium in interface box.$flg_intf_atm==1
my %hash_modf_intf_indv_amt;            # amount for each individual modifer in interface box.$flg_intf_atm==1
my %hash_modifier_cn_exbox_tot_amt;     #total CN for calcium in interface box.$flg_intf_atm==2
my %hash_modf_exbox_indv_amt;           # amount for each individual modifier in extended box. $flg_intf_atm==2
my %hash_former_indv_CN_cnt;            # CN for individual former in interface box
my %hash_former_exbox_indv_CN_cnt;      # CN for individual former in extended box
my %hash_former_indv_Qn_cnt;            # Qn for individual former in interface box
my %hash_former_exbox_indv_Qn_cnt;      # Qn for individual former in extended box
#my %hash_former_cn_err;                 #total CN for formers whose CN is out of range
#my %hash_modifer_cn_err;                #total CN for modifiers whose CN is out of range
#my %hash_oxygen_cn_err;                 #total CN for oxygens whose CN is out of range
my $flg_former;                         #flag former or not. 1:former; 0: non-former
my @cn;                                 #2D array. $cn[$atom_id][cn]
my @qn;                                 #2D array. $qn[$atom_id][qn]
my $sampling_start_time;                #starting time of a sample. will be converted into frame number
my $sampling_end_time;                  #ending time of a sample. will be converted into frame number
my $sampling_start_timestep_no;         #starting # of timesteps
my $sampling_start_frame_no;            #starting frame number of a sample, =starting # of timesteps/$dump_gap
my $sampling_end_timestep_no;           #ending # of timesteps
my $sampling_end_frame_no;              #ending frame number of a sample, =ending # of timesteps/$dump_gap
my $search_loop_limit;                  #when this value is reached, exit loop
my $run_no_timestep;                    #number of timesteps in LAMMPS in file. the number after command "run"
my $sampling_size;                      #size of a sample
my $sampling_indx_start_dir;            #index for starting directory in @dirs
my $sampling_indx_end_dir;              #index for ending directory in @dirs
my $dir_loop_i;                         #loop index
my $cnt_frame;                          #count frames to get the mean value of CN and Qn
my $fram_amt_stat;                      #frame amount which is used to calculate CN/Qn distribution. CN=TOT_CN/$fram_amt_stat
my $indx_line_no_ini_frm;               # the 1st line number of the first/start frame, to control sampling frames while CN/Qn analysis performing, for tracking, value is 0
my $indx_line_no_last_frm;              # the 1st line number of the last/end frame, to control sampling frames while CN/Qn analysis performing, for tracking, value is $line_no[$#line_no];
my $amt_atm_interfacebox;               #amount of atoms in the interface box
my $amt_atm_extendedbox;                #amount of atoms in the extended box
my $amt_o_nearby_modifier;              #amount of oxygen nearby modifers, like Ca
my @atm_id_o_nearby_modifier;           #oxygen atom id nearby modifers

INFO:
#print colored("$0","bold cyan")," is used to analyze CN and/or Qn distribution, meanwhile output CN and/or Qn for each target species, like former(Si/Al/...) and oxygen.\n";
print "$0 is used to analyze CN and/or Qn distribution, meanwhile output CN and/or Qn for each target species, like former(Si/Al/...) and oxygen.\n";
#print colored("$0 consider periodic boundary. All bond length calculated based on periodic boundary.\n","bold yellow");
print "$0 consider periodic boundary. All bond length calculated based on periodic boundary.\n";
print "Please run $0 at parents directory which consists of simulating directories, such as 500kstp, 1mstp, 1.5mstp, etc.\n";

CONTROL_VARIFICATION:
###########################################################################################################################
# To efficiently read data and allow user to run program on the computing node
# this program will read parameter from a input_control.in file
# each line has its notation. User should follow the order and rule to update it.
###########################################################################################################################
if(-e $input_control_file)
{$flag=1;}
else
{ $flag=0;$error_msg="$error_msg\tNo input control file found $input_control_file;";
  print colored("Warning","bold yellow blink"),": $input_control_file is REQUIRED for parameters. No $input_control_file exists in $work_dir, please double check it.Quit.\n";
}

### write commands to command file for record later
my $datelog=`date`;
$datelog=tm::trim($datelog);
 

MAIN:
##################################################################################################
#################  MAIN ##################
if($flag == 1)
{
  my $total_line;
  my @line_no;
  my $first_line_frm;my$last_line_frm;          #first and last line # of each frame

  CONFIG:
  ##################################################################################################
  # collect parameters from input_control file
  ##################################################################################################
  INPUT_CONTROL_IN:
  open(INPUT_CONTROL, "< $input_control_file");
  $i=0;
  while ($line=<INPUT_CONTROL>)
  {
    $line=tm::trim($line);
    #@values=split(/\s+/,$line);chomp(@values);
    @values=split(/\#/,$line);chomp(@values);
    $sub_values[$i]=tm::trim($values[0]);         #read the first column and remove all spaces before and after the value
    $i++;
  }#end while ($line=<INPUT_CONTROL>)
  $ctrl_flg_command_tgt_id  = $sub_values[0];     #which command(BL/CN) will be excuted based on the given number.>0, BL; <=0 CN & Qn
  $ctrl_flg_exist_vacuum    = $sub_values[1];     # flag for vacuum layer UV: vacuum exist upper/bottom box, NV: no vacuum layer, IV: vacuum exist inside
  $ctrl_flg_varify_data     = $sub_values[2];     #flag for varify data files. Y: verified; N: non-varified/need to reverify
  $ctrl_flg_search_all_nghb = $sub_values[3];     #flag for searching all neighbors. 1: all; 0: interested ONLY
  $ctrl_formers             = $sub_values[4];     #former lists
  $ctrl_modifers            = $sub_values[5];     #modifier lists
  $ctrl_sim_dir_keyword     = $sub_values[6];     #keyword in simulating directory, like .../500kstp/
  $ctrl_anly_dir            = $sub_values[7];     #analyzing dirctory name in simulating directory, like "newzdp" in.../500kstp/newzdp/, here is "newzdp"
  $ctrl_dump_struc_file     = $sub_values[8];     #dump file name
  $ctrl_dir_trck            = $sub_values[9];     #tracking directory name
  $ctrl_comp_keyword        = $sub_values[10];     #common keyword for compositions, like comp_1, comp_2.....
  $ctrl_Lanalysis           = $sub_values[11];     #control file for zdp, bat, and His/DLpoly file
  $ctrl_model_info_file     = $sub_values[12];     #model_info.log which consists of total atom number,glass & water atom amount,thickness of interface box
  $ctrl_orientation_trunk   = $sub_values[13];     #axis of surface cut perpendiculared to. 
  $ctrl_search_depth        = $sub_values[14];    #sedarch depth
  $ctrl_lammps_in_file      = $sub_values[15];    #LAMMPS in file
  $ctrl_starting_time_sampling = $sub_values[16]; #unit fs. for CN/Qn distribution, will be converted into frame number
  $ctrl_ending_time_sampling   = $sub_values[17]; #unit fs. for CN/Qn distribution, will be converted into frame number
  $ctrl_loop_tstp_sampling  = $sub_values[18];    #loop step, only for CN/Qn analysis with LIMITED frames($flg_BL<0).other analysis =0
  $ctrl_loop_max_time_sampling   = $sub_values[19];    #maximum sampling time
  $ctrl_max_cn              = $sub_values[20];    #maximum cn values between all species, like formers, modifers, oxygen

  ### set variables based on read parameters above
  if($ctrl_flg_command_tgt_id>0)
  { 
    $target_atom_id=$ctrl_flg_command_tgt_id;
    $flg_BL=1;
    $ctrl_loop_tstp_sampling=0;     #no time loop required for BL analysis
  }#end if($ctrl_flg_command_tgt_id>0)
  elsif($ctrl_flg_command_tgt_id==0)
  { $flg_BL=0;
    $ctrl_loop_tstp_sampling=0;     #no time loop required for CN/Qn analysis with a certain amount frames
  } # CN/Qn distribution, no output info for each atom in the interface box
  else{$flg_BL=-1;}                 # CN/Qn distribution, output each atom info for each atom in the interface box

  if(uc($ctrl_flg_exist_vacuum) eq 'UV')      #vacuum locates upper or bottom box not in the middle like a sandwich
  {$flg_vacuum=1;}#end if(uc($ctrl_flg_exist_vacuum) eq 'UV')
  elsif(uc($ctrl_flg_exist_vacuum) eq 'NV')   #no vacuum
  {$flg_vacuum=0;}#end elsif(uc($ctrl_flg_exist_vacuum) eq 'NV')
  elsif(uc($ctrl_flg_exist_vacuum) eq 'IV')   #like a sandwich.NO READY.NOT TEST.NO MODULES
  {$flg_vacuum=-1;} 
  else
  { print "Error. Incorrect setting for vacuum layer. It should be 'NV' (no vacuum),'EV'(vacuum locate upper/bottom box), and 'IV'(vacuum locates inside like a sandwich). Quit.\n"; 
    $error_msg="$error_msg;Incorrect setting for vacuum layer. It should be 'NV' (no vacuum),'EV'(vacuum locate upper/bottom box), and 'IV'(vacuum locates inside like a sandwich)";
    $flag=0;goto MAIN;
  }
 
  if(uc(substr($ctrl_flg_search_all_nghb,0,1)) eq "A"){$flg_srch_all_nghb=1;}
  else{$flg_srch_all_nghb=0;}


  ### parse species list
  $ctrl_formers=uc($ctrl_formers);
  $ctrl_modifers=uc($ctrl_modifers);
  @former_lists=split(/\s+/,$ctrl_formers);chomp(@former_lists);
  @modifer_lists=split(/\s+/,$ctrl_modifers);chomp(@modifer_lists);

  #initialize cn and qn hash
  for($i=-1;$i<=$ctrl_max_cn;$i++)    #here,CN starts from -1, if CN is out of range, will be saved to -1
  { 
      # initialize variables for total counting
      $hash_former_cn_tot_amt{$i}=0;$hash_former_exbox_cn_tot_amt{$i}=0;$hash_former_qn_tot_amt{$i}=0;$hash_former_exbox_qn_tot_amt{$i}=0;
      $hash_oxygen_cn_tot_amt{$i}=0;
      $hash_oxygen_cn_exbox_tot_amt{$i}=0;      
      $hash_oxygen_cn_glass_tot_amt{$i}=0;      
      $hash_oxygen_cn_glass_exbox_tot_amt{$i}=0;
      $hash_oxygen_cn_water_tot_amt{$i}=0;      
      $hash_oxygen_cn_water_exbox_tot_amt{$i}=0;
      $hash_modifier_cn_tot_amt{$i}=0;           
      $hash_modifier_cn_exbox_tot_amt{$i}=0;     

      # initialize variables for individual counting
      foreach(@former_lists)
      {
        $hash_former_indv_CN_cnt{$_}{$i}=0;
        $hash_former_exbox_indv_CN_cnt{$_}{$i}=0;
        $hash_former_indv_Qn_cnt{$_}{$i}=0;
        $hash_former_exbox_indv_Qn_cnt{$_}{$i}=0;
      }#end foreach(@former_lists)
  }#end for($i=-1;$i<=$ctrl_max_cn;$i++) 

  #intialize hash value
  foreach (@former_lists)
  {$former_cnt{$_}=0;$hash_former_intf_indv_amt{$_}=0;$hash_former_exbox_indv_amt{$_}=0;}
  foreach (@modifer_lists)
  {$hash_modf_intf_indv_amt{$_}=0;$hash_modf_exbox_indv_amt{$_}=0;} 
 
 
  chomp($ctrl_dir_trck); 
  if( !-d "$work_dir/$ctrl_dir_trck" ){system("mkdir $work_dir/$ctrl_dir_trck");}
  else{;}

  DUMP_ALL_LAMMPSTRJ:
  #### collect info from LAMMPS input file
  if(-e $ctrl_lammps_in_file)
  {
    ### get timestep
    $line=`grep timestep < $ctrl_lammps_in_file|grep -v "#"`;$line=tm::trim($line);
    if(length($line)<1){$flag=0;$error_msg="$error_msg;there is # in timestep line in LAMMPS control file,remove # and its rest part";print "there is notation symbol # in 'run' command line in LAMMPS control file $ctrl_lammps_in_file, Please remove '#' and its rest part.\n";}
    @values=split(/\s+/,$line);chomp(@values);
    $time_step=$values[1];       #timestep
    
    ### get dump dump_gap/frequency
    $line=`grep dump < $ctrl_lammps_in_file | grep -v "#"`;$line=tm::trim($line);
    if(length($line)<1){$flag=0;$error_msg="$error_msg;there is # in dump command line in LAMMPS control file,remove # and its rest part";print "there is notation symbol # in 'run' command line in LAMMPS control file $ctrl_lammps_in_file, Please remove '#' and its rest part.\n";}
    @values=split(/\s+/,$line);chomp(@values);
    $dump_gap=$values[4];                 #how many timesteps to dump one trojectory
    ## check whether it is a number
    if($dump_gap =~ /\d+/){print "dump gap is $dump_gap\n";}
    else{print "dump gap is not a valid number. quit.\n";$flag=0;$error_msg="$error_msg\tdump gap is invalid number;";}
    
    ### get # of timesteps
    $line=`grep run < $ctrl_lammps_in_file|grep -v "#"`;$line=tm::trim($line);
    if(length($line)<1){$flag=0;$error_msg="$error_msg;there is # in run command line in LAMMPS control file,remove # and its rest part";print "there is notation symbol # in 'run' command line in LAMMPS control file $ctrl_lammps_in_file, Please remove '#' and its rest part.\n";}
    @values=split(/\s+/,$line);chomp(@values);
    $run_no_timestep=$values[1];       # number of timestep, the number after command "run"
  }
  else
  {print "Error. LAMMPS control file $ctrl_lammps_in_file does NOT exist.Quit.\n";$flag=0;$error_msg="$error_msg\tNo $ctrl_lammps_in_file in $work_dir;";}

  ############## collect all info
  ### collect simulation directories
  WORK_ENVIRONMENT: 
  #collect composition number
  if($work_dir=~ /$ctrl_comp_keyword/)
  {
    $flag=1;
    @values=split(/$ctrl_comp_keyword/,$work_dir);chomp @values;
    @sub_values=split(/\//,$values[1]);chomp @sub_values;
    $comp_id=$sub_values[0];
  }#end if($work_dir=~ /comp_/)
  else
  { $flag=0; $error_msg="$error_msg"."keyword comp is not available in $work_dir";
  }#else of if($work_dir=~ /comp_/)
  
  print colored("PLEASE CHECK SIMULATION DIRECTORIES BELOW WHICH CONSITS OF ","BOLD YELLOW"),colored("newzdp","bold magenta"),"\n";
  $line=`ls |grep $ctrl_sim_dir_keyword|sort -n`;chomp($line);
  @values=split(/\r?\n/,$line);chomp(@values);
  $input=pop(@values);
  unshift(@values,$input);
  @dirs=@values;

  BREAKPOINT:
  #### BREAKPOINT for accidentally quit
  #### for 500kstp, 1mstp,...#stp
  #### #*2 and replace the value xxx in $i<=xxx, update $sn_frame using last FRAM_# shown in related file
  #for($i=1;$i<=29;$i++){shift @dirs;}    #delete here is for resume analysis
  #$sn_frame=14500000;
  ### END BREAKPOINT

  INSPECTION_INITIALIZATION:
  ### inspect the directory and file correction
  $i=1;
  ## list directories
  foreach $dir (@dirs)
  {if ($i%10 ==0){printf "%11s\n",$dir;}else{printf "%11s",$dir;}$i++;}
  $i--;
  print "\ntotal directory number is ",colored("$i\n","bold cyan");
  print "************* END CHECK ***************\n"; 
  print "Please check above simulating directories. If anything is wrong, input <CTRL>+Z or <CTRL>+X to quit.\n";

 
##for auto run#   if(uc($ctrl_flg_varify_data) eq "Y")
##for auto run#   {
    #$_=<STDIN>;
    ##for auto run##name of target species
    ##for auto run#if (-d "rct_trk")
    ##for auto run#{
    ##for auto run#  #read tot_comp*.dat file to achieve names of a target species/atomId
    ##for auto run#  $line=`cat $work_dir/rct_trk/tot_comp_*.dat`;chomp($line); @values=split(/\r?\n/,$line);chomp(@values);
    ##for auto run#  $i=0;
    ##for auto run#  foreach(@values)
    ##for auto run#  {
    ##for auto run#    @sub_values=split(/\s+/,$_);chomp(@sub_values);
    ##for auto run#    $species[$i]=$sub_values[7];
    ##for auto run#    $tgt_atm_ids[$i]=$sub_values[6];
    ##for auto run#    $i++;
    ##for auto run#  }#end foreach(@values)
    ##for auto run#}#if (-d rct_trk)
    ##for auto run#else
    ##for auto run#{
    ##for auto run#  print "tot_comp_*.dat files do not exist in $work_dir/rct_trk.";
    ##for auto run#  print "Input target species: ";
    ##for auto run#  $input=<STDIN>;chomp($input);
    ##for auto run#  if($input =~ /^[a-z,.A-Z]+$/)
    ##for auto run#  {$spc=$input;}
    ##for auto run#  else
    ##for auto run#  {$flag=0;$error_msg="$error_msg;"."Input($input) illegal";print colored("$input","bold red"),colored(" should be alphabets.Quit.\n","bold yellow");}
    ##for auto run#
    ##for auto run#
    ##for auto run#  print "Input target atom ID: ";
    ##for auto run#  $input=<STDIN>;chomp($input);
    ##for auto run#  #if ($input=~ /^[0-9,.E,.e]+$/){$target_atom_id=$input;}
    ##for auto run#  if ($input=~ /^[0-9]$/){$target_atom_id=$input;}
    ##for auto run#  else{$flag=0;$error_msg="$error_msg;"."No numberic input (user input: $input)";print "Your input is ",colored("$input","bold red"),". ",colored("Input should be all digital numbers.Error.Quit!\n","bold yellow");}
    ##for auto run#}#end else of if (-d rct_trk)
##for auto run#   }#end if(uc($ctrl_flg_varify_data) eq "Y")
  
  $file_input_struc=$ctrl_dump_struc_file;

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
    $sim_dir="$work_dir/$dir/$ctrl_anly_dir";
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
        else    #read element lists: $_[0] - type; $_[1] - element
        { #set hash variables
          $spc_type[$_[0]]=$_[1];$hash_type_spc{$_[0]}=$_[1];$hash_spc_type{$_[1]}=$_[0];
          print"\$spc_type[$i]=$spc_type[$i]\n";
        }#end else of if($input=~ /end type/)
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
    if(uc($ctrl_flg_varify_data) eq "Y")        #need to verify data
    {$flg_rescan_dump=1;
    }#if(uc($ctrl_flg_varify_data) eq "Y")      
    else                                        #do not need to verify data
    {$flg_rescan_dump=0;
    }#end else of if(uc($ctrl_flg_varify_data) eq "Y")

    if(-e "dump.all.lammpstrj.stat" and $flg_rescan_dump==0)
    { 
      system("echo ''; ls -l 'dump.all.lammpstrj.stat';");#cat dump.all.lammpstrj.stat;");
      $flg_rescan_dump=-1;
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
      if(-e "$work_dir/$ctrl_model_info_file")
      {
        $ctrl_model_info_file="$work_dir/$ctrl_model_info_file";
      }#end if(-e $work_dir/$ctrl_model_info_file)
      else
      #elsif(-e "$sim_dir/$ctrl_model_info_file")
      { foreach (@dirs) 
        { $tmp="$work_dir/$_/$ctrl_anly_dir";
          if(-e "$tmp/$ctrl_model_info_file"){$ctrl_model_info_file="$tmp/$ctrl_model_info_file";exit;}
          else{next;}#end else of if(-e "$tmp/$ctrl_model_info_file")
        }#end foreach (@dirs)

        #if file exists, read parameters, or quit
        chomp($ctrl_model_info_file);
      }#end else of if(-e "$work_dir/$ctrl_model_info_file")
 
      if(length($ctrl_model_info_file)==0)
      {$error_msg="$error_msg$ctrl_model_info_file does not exist in $work_dir or $sim_dir;";$flag=0; goto MAIN;}
      else
      {
        $line=`head -1 $ctrl_model_info_file`;$line=tm::trim($line);             #read atom amount in glass
        @values=split(/\s+/,$line);chomp(@values);
        $atm_amt_glass=$values[$#values];
        $line=`head -2 $ctrl_model_info_file|tail -1`;$line=tm::trim($line);
        @values=split(/\s+/,$line);chomp(@values);
        $atm_amt_water=$values[$#values];
        $atm_amt_tot=$atm_amt_glass+$atm_amt_water;
        $line=`tail -3 $ctrl_model_info_file |head -2`;$line=tm::trim($line);    #extract info for up_g,lo_g,up_w,and lo_w
        @values=split(/\r|\n/,$line);chomp(@values);
        for(my $ss=0;$ss<=$#values;$ss++)                 #remove spaces in each line
        { $values[$ss]=tm::trim($values[$ss]);
          @_=split(/\s+/,$values[$ss]);chomp(@_);

          # NOTE: here, the setting is only for surface analysis
          # For bulk analysis, to avoid boundary issue, new variables are employed to improperly avoid changing the value of parameter
          if($ss==0){$up_g=$_[1];$lo_g=$_[3];}
          else{$up_w=$_[1];$lo_w=$_[3];}
        }
      }#end else of if(length($ctrl_model_info_file)==0)
    }#end if ($up_g==-1 or $up_w==-1 or $lo_g==-1 or $lo_w==-1)
  }#end foreach $dir (@dirs) 

   print "If you think the file info shown above may have been changed. Please ENTER <CTRL>+Z or <CTRL>+X to quit and set the 2nd line to ",colored("Y","bold blink yellow"),".\n";
#    print "No problem confirmed by user.\n";


#  print colored("Please check above file size which should be same or very close each other.\n","bold yellow");
#  print "Is there anything wrong?(y/n, ENTER for no) ";
#  ##for auto run#$input=<STDIN>;$input=tm::trim($input);
#  $input='n';
#  if(length($input) == 0){print "\nNo error reported. Continue.\n";}
#  elsif(uc($input) eq "Y" or uc($input) eq "YES"){$flag=0;$error_msg="$error_msg;user report size of $file_input_struc error";print "\nUser reported size of $file_input_struc does NOT match each other. Quit.\n";}
#  elsif(uc($input) eq "N" or uc($input) eq "NO"){print "\nUser confirmed no errors.\n";}
#  else{print "\nInvalid input. Choose defualt no error occured. Continuing. \n";}
  
  print "Input trunking orientation (x/y/z,ENTER for default z orientation) ";
  $input=$ctrl_orientation_trunk;print "\n";
  if(length($input) == 0){print "User choose to trunk along z orientation.\n";$flg_interface=-3;}     #surface analysis along z
  elsif(uc($input) eq 'Z'){print "User choose to trunk along z orientation.\n";$flg_interface=-3;}    #surface analysis along z
  elsif(uc($input) eq 'Y'){print "User choose to trunk along y orientation.\n";$flg_interface=-2;}    #surface analysis along y
  elsif(uc($input) eq 'X'){print "User choose to trunk along x orientation.\n";$flg_interface=-1; }   #surface analysis along x
  elsif(uc($input) eq 'XYZ'){print "User choose to trunk along z orientation.\n";$flg_interface=3;}   #bulk analysis along z
  elsif(uc($input) eq 'ZXY'){print "User choose to trunk along z orientation.\n";$flg_interface=2;}   #bulk analysis along y
  elsif(uc($input) eq 'YZX'){print "User choose to trunk along z orientation.\n";$flg_interface=1;}   #bulk analysis along x
  else{print "User choose to extend the imaging box along x,y,z. CTRL+C or CTRL+Z to cancel this program.\n";$flg_interface=0;} #3D 
  
  print "Collecting required information from $file_input_struc in $dirs[0] and $dirs[$#dirs], please wait ...\n"; 
 
  ### check timestep limits      
  $tmp="$work_dir/$dirs[0]/$ctrl_anly_dir/$file_input_struc";
  $_=`grep -A 1 TIMESTEP $tmp |head -2 |tail -1`;chomp($_);
  $timestep_min=$_;              
  $time_min=$timestep_min*$time_step;
  $tmp="$work_dir/$dirs[$#dirs]/$ctrl_anly_dir/$file_input_struc";
  $_=`grep -A 1 TIMESTEP $tmp |tail -1`;chomp($_);
  $timestep_max=$_;              
  $time_max=$timestep_max*$time_step;

  $time_gap=$dump_gap*$time_step;

  #########################
  # time set by user will be converted into TIMESTEP which is used in dump file
  # however, such value may not be an integer number 
  # to resolve this issue
  # based on user's setting, the timestep will be convert to valid value shown in dump file
  if($ctrl_starting_time_sampling%$time_gap != 0)   #time can not be divided by $time_gap into integer
  {
    if($ctrl_starting_time_sampling > $time_min)
    { $_=$ctrl_starting_time_sampling-($ctrl_starting_time_sampling % $time_gap); 
      $warn_msg="$warn_msg;invalid starting time ($ctrl_starting_time_sampling fs) for sampling. Program changed it into $_";
      print "invalid starting time ($ctrl_starting_time_sampling fs) for sampling. Program changed it into $_.\n";
      $ctrl_starting_time_sampling=$_;
    }#end if($ctrl_starting_time_sampling > $time_min)
    else
    { $warn_msg="$warn_msg;starting time ($ctrl_starting_time_sampling fs) out of limits. set it into $time_min";
      print "starting time ($ctrl_starting_time_sampling fs) out of limits. set it into $time_min.\n";
      $ctrl_starting_time_sampling=$time_min;
    }#end else of if($ctrl_starting_time_sampling > $time_min)
  }#end if($ctrl_starting_time_sampling%$time_gap != 0)
  else
  {
    if($ctrl_starting_time_sampling < $time_min)
    { $warn_msg="$warn_msg;starting time ($ctrl_starting_time_sampling fs) out of limits. set it into $time_min";
      print "starting time ($ctrl_starting_time_sampling fs) out of limits. set it into $time_min.\n";
      $ctrl_starting_time_sampling=$time_min;
    }#end else of if($ctrl_starting_time_sampling < $time_min)
  }#end else of if($ctrl_starting_time_sampling%$time_gap != 0)

  if($ctrl_ending_time_sampling%$time_gap != 0)   #time can not be divided by $time_gap into integer
  {
    if($ctrl_ending_time_sampling < $time_max)
    { $_=$ctrl_ending_time_sampling+($time_gap - $ctrl_ending_time_sampling % $time_gap); 
      $warn_msg="$warn_msg;invalid ending time ($ctrl_ending_time_sampling fs) for sampling. Program changed it into $_";
      print "invalid ending time ($ctrl_ending_time_sampling fs) for sampling. Program changed it into $_.\n";
      $ctrl_ending_time_sampling=$_;
    }#end if($ctrl_ending_time_sampling < $time_max)
    else
    { $warn_msg="$warn_msg;ending time ($ctrl_ending_time_sampling fs) out of limits. set it into $time_max";
      print "ending time ($ctrl_ending_time_sampling fs) out of limits. set it into $time_max.\n";
      $ctrl_ending_time_sampling=$time_max;
    }#end else of if($ctrl_ending_time_sampling < $time_max)
  }#end if($ctrl_ending_time_sampling%$time_gap != 0)
  else
  {
    if($ctrl_ending_time_sampling > $time_max)
    { $warn_msg="$warn_msg;ending time ($ctrl_ending_time_sampling fs) out of limits. set it into $time_max";
      print "ending time ($ctrl_ending_time_sampling fs) out of limits. set it into $time_max.\n";
      $ctrl_ending_time_sampling=$time_max;
    }#end else of if($ctrl_ending_time_sampling > $time_max)
    else{;}
  }#end else of if($ctrl_ending_time_sampling%$time_gap != 0)
 
#del print "705
#del \$sampling_start_timestep_no=$ctrl_starting_time_sampling/$time_step=$sampling_start_timestep_no;
#del \$sampling_start_frame_no=$sampling_start_timestep_no\/$dump_gap=$sampling_start_frame_no;
#del \$sampling_end_timestep_no=$ctrl_ending_time_sampling/$time_step=$sampling_end_timestep_no;
#del \$sampling_end_frame_no=$sampling_end_timestep_no\/$dump_gap=$sampling_end_frame_no;
#del \$sampling_size=($sampling_end_timestep_no-$sampling_start_timestep_no+$dump_gap)/$dump_gap=$sampling_size;
#del \$sampling_indx_start_dir=int($sampling_start_timestep_no/$run_no_timestep)=$sampling_indx_start_dir;\t $dirs[$sampling_indx_start_dir];
#del \$sampling_indx_end_dir=int($sampling_end_timestep_no/$run_no_timestep)=$sampling_indx_end_dir;\t$dirs[$sampling_indx_end_dir];
#del \$_=$_\n";
#del $_=<STDIN>;
 

  ## input of target atom id will be improved in automatic or manual ways
  ## neighbor id will be improved in the future
  ## print "Input target atom ID: ";
  ## $input=`cat target_in.dat`;chomp($input);$input=tm::trim($input);print"\n";
  ## ##for auto run#$input=<STDIN>;chomp $input;$input=tm::trim($input);$_=$input;
  ## #if(length($input) eq 0 or $input =~ s/\D//g){$flag=0;print "Invalid atom ID($_). Quit.\n";$error_msg="$error_msg"."Invalid atom ID: $_";}
  ## if(length($input) eq 0 or $input =~ s/\D//g){$flag=0;print "Invalid atom ID($_). Quit.\n";$error_msg="$error_msg"."Invalid atom ID: $_";}
  ## else{$target_atom_id=$input;print "User input target atom ID:",colored("$target_atom_id","bold cyan"),".\n";}
  
  ####cutoff setting to determine neighbors
  ###print "Input cutoff value (ENTER for default $DFT_CUTOFF A): ";
  ###$input=<STDIN>;chomp($input);$_=$input;
  ####if ($input=~ /^[0-9,.E,.e]+$/){$cutoff=$input;}
  ###if (length($input) == 0){$cutoff=$DFT_CUTOFF;}
  ###elsif($input=~ /\d/){$cutoff=$input;}
  ###else{$flag=0;$error_msg="$error_msg;"."No numberic input (user input: $input)";print "Your input is ",colored("$input","bold red"),". ",colored("Input should be all digital numbers.Error.Quit!\n","bold yellow");}
  
  foreach $input (keys (%hash_cutoff))
  { printf "cutoff between types:%5s ==> %.3f A\n",$input,$hash_cutoff{$input};
    if($max_cutoff<$hash_cutoff{$input}){$max_cutoff=$hash_cutoff{$input};}
  }#end foreach $input (keys (%hash_cutoff))

  #if($flg_interface==3){$cutoff_xyz=$max_cutoff;}
  $cutoff_xyz=$max_cutoff;

  #to reuse those codes for surface analysis, here the parameter will be forcefully updated
  if($flg_vacuum==1)          #UV: vacuum locates in upper/bottom box
  { 
    if($flg_interface>0)      #bulk analysis
    {$lower_threshold=$max_cutoff;$upper_threshold=$lo_g;}
    elsif($flg_interface==0)  #3D
    {;}
    else                      #surface analysis
    {$lower_threshold=$lo_g;$upper_threshold=$up_w;}
  }#end if($flg_vacuum==1)
  elsif($flg_vacuum==0)   #NV: no vacuum
  {;}
  elsif($flg_vacuum==-1)  #IV: vacuum inside the box somewhere, NOT TESTED
  {
    print "Models with inside vacuum have not been tested.\nTo help you analyze your models accurately, Please contact Dr. Liaoyuan Wang at wly_ustc\@hotmail.com\n";
    if($flg_interface>0)      #bulk analysis
    {$lower_threshold=$max_cutoff;$upper_threshold=$ccc;}
    elsif($flg_interface==0)  #3D
    {;}
    else                      #surface analysis
    {$lower_threshold=$lo_g;$upper_threshold=$up_w;}
  }#end elsif($flg_vacuum==-1)
  else
  {;} 


  ################################################################################
  ############## info for user
  print "Current work directory ",colored("$work_dir","bold yellow"),".\n\nBelow are simulating directories:\n";

  system("ls -latr \"$work_dir\"|grep \"$ctrl_sim_dir_keyword\";echo ''; ");

  print colored("ATTENTION:","bold yellow blink"),colored("User MUST check settings and confirm the settings consistent with your simulations, such as KEYWORDS of\n\nkeywords in simulating folder: ","bold magenta"),colored("$ctrl_sim_dir_keyword","bold yellow"),colored(" \nanalyzing folder : ","bold magenta"),colored(".../\*$ctrl_sim_dir_keyword\*/newzdp","bold yellow"),colored("\ntracking_analysis_dirctory : ","bold magenta"),colored("$ctrl_dir_trck","bold yellow"),colored(" \ntrojectory file name : ","bold magenta"),colored("$ctrl_dump_struc_file","bold yellow"),colored(" \ntimest: ","bold magenta"),colored("$time_step","bold yellow"),colored("(fs) \ndump_gap:","bold magenta"),colored("every ","bold cyan"),colored("$dump_gap","bold yellow"),colored(" extract one frame \n","bold cyan"),colored("abbrevation of composition: ","bold magenta"),colored("$ctrl_comp_keyword","bold yellow"),colored("\n...\n\n","bold magenta");
  print colored("If anything wrong, please check your input control file \"$input_control_file\".\n","bold yellow");
  
  ################################################################################

  if($flg_BL<0)     #set @sampling_t_lists. CN/Qn analysis for limited amount of frames
  {
    $j=0;
    $_=$ctrl_starting_time_sampling;
    while ($_<=$ctrl_loop_max_time_sampling)
    {
      $_=$_+$j*$ctrl_loop_tstp_sampling;
      push(@sampling_t_lists,$_);
print"1104 $j\t$sampling_t_lists[$j]\t\$time_step=$time_step\t\$dump_gap=$dump_gap\n";$tmp=<STDIN>;
      $j++;
    }#end while ($_<=$ctrl_loop_max_time_sampling)
  }#end if($flg_BL<0)     ##set @sampling_t_lists. CN/Qn analysis for limited amount of frames
  else      #BL analysis and CN/Qn analysis for a certain amount of frames
  {
      push(@sampling_t_lists,$$ctrl_starting_time_sampling);
      push(@sampling_t_lists,$ctrl_ending_time_sampling);
  }
  
################################################################################
############## read lammpstrj and convert coordinates
  print "Counting frame number and line number. Please wait ...\n";
  chomp@line_no;
 
  for($sampling_t_loop_i=0;$sampling_t_loop_i<$#sampling_t_lists;$sampling_t_loop_i++)
  { 
    $ctrl_starting_time_sampling=$sampling_t_lists[$sampling_t_loop_i];
    $ctrl_ending_time_sampling=$sampling_t_lists[$sampling_t_loop_i]+$time_step*$dump_gap;
    $sampling_start_timestep_no=$ctrl_starting_time_sampling/$time_step;                #starting timestep of a sample. the value below TIMESTEP in dump file
    $sampling_start_frame_no=$sampling_start_timestep_no/$dump_gap;                     #starting frame number. it is the SN of frames at the starting timestep
  
    $sampling_end_timestep_no=$ctrl_ending_time_sampling/$time_step;                    #ending timestep of a sample. the value below TIMESTEP in dump file
    $sampling_end_frame_no=$sampling_end_timestep_no/$dump_gap;                         #ending frame number. It is the SN of frames at the ending timestep
  
    $sampling_size=($sampling_end_timestep_no-$sampling_start_timestep_no+$dump_gap)/$dump_gap;
    $sampling_indx_start_dir=int($sampling_start_timestep_no/$run_no_timestep);$_=$sampling_start_timestep_no%$run_no_timestep;
    if($_==0 and $ctrl_starting_time_sampling>0){$sampling_indx_start_dir--;}
    $sampling_indx_end_dir=int($sampling_end_timestep_no/$run_no_timestep);$_=$sampling_end_timestep_no%$run_no_timestep;
    if($_==0 and $ctrl_ending_time_sampling>0){$sampling_indx_end_dir--;}
    
    ### check data is in the limit or not
    if($sampling_indx_end_dir > $#dirs or $sampling_indx_start_dir < 0)
    { $flag=0;$error_msg="$error_msg sampling time range ($ctrl_starting_time_sampling-$ctrl_ending_time_sampling) is out of the limit;";
      print "Sampling time range $ctrl_starting_time_sampling-$ctrl_ending_time_sampling is out of limits. Quit.\n";
      exit;
    }#end if($sampling_indx_end_dir > $#dirs or $sampling_indx_start_dir < 0)

    ### There are two types of analyse in this program
    ### each analysis has similar codes
    ### to efficiently use these codes, some parameters need to be set based on analysis
    ### set output file names
    SETTING_BL_ANALYSIS:
      if ($flg_BL ==1)        #BL analysis and tracking analysis
      {
        ###output file name
        $output_bondlength_file="$work_dir/$ctrl_dir_trck/$target_atom_id\_bondlength.dat";
        
        if(-e $output_bondlength_file){tm::rename($output_bondlength_file);}#if file exist, rename it based on current time
    
        open(OUTPUT,">$output_bondlength_file");
    
        #each line the data set may be varied, here, only give title rule
        print OUTPUT "FrameNO\tTitle Rule: Frame# time(fs) CN [Qn] LabelOfTargetType (PRMRYTGT or SBSDRYTGT)\tTargetAtomID\tTargetAtomName\tNeighborAtomID\tNeighborAtomName\tBondLenght\tNeighborAtomID\t...\n";
        print  "FrameNO\ttime(fs)\tCN [Qn]\tLabel\tPrimaryTargetID\tPrimaryTargetName\tNeighborAtomID\tNeighborAtomName\tBondLength ...\n";
    
        ### set the initial and final index for @dirs
        #here, for BL analysis, all elements in @dirs will be visited
        $sampling_indx_start_dir=0;
        $sampling_indx_end_dir=$#dirs;
      }#end if ($flg_BL ==1)
      else                                #CN/Qn analysis
      {
        ### output atom id if CN <> Qn
        if($flg_interface<=0)    #surface analysis
        {
          if($flg_BL==0)
          {
            $file_former_cn_NE_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_cn_NE_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
            $file_former_cn_EQ_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_cn_EQ_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
            $file_former_id_cn_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_former_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
            $file_modifier_id_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_modifer_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
            $file_oxygen_id_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_oxyg_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
            $file_hydrogen_id_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_hydrg_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
            $file_all_spc_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_all_spc_cn.$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          }#end if($flg_BL==0) CN/Qn analysis for a certain number of frames (>=5)
          else
          {
            $file_former_cn_NE_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_cn_NE_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
            $file_former_cn_EQ_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_cn_EQ_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
            $file_former_id_cn_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_former_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
            $file_modifier_id_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_modifer_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
            $file_oxygen_id_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_oxyg_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
            $file_hydrogen_id_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_hydrg_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
            $file_all_spc_cn="$work_dir/$ctrl_dir_trck/cs$comp_id\_all_spc_cn.$sampling_start_timestep_no-$sampling_end_timestep_no-$ctrl_loop_tstp_sampling-$ctrl_loop_max_time_sampling.dat";
          }#end else of if($flg_BL==0) CN/Qn analysis for a certain number of frames (<=5)
        }#end if($flg_interface<=0)    #surface analysis
        else    #here $flg_interface==3 bulk analysis
        {
          $file_former_cn_NE_qn="$work_dir/$ctrl_dir_trck/cb$comp_id\_cn_NE_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          $file_former_cn_EQ_qn="$work_dir/$ctrl_dir_trck/cb$comp_id\_cn_EQ_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          $file_former_id_cn_qn="$work_dir/$ctrl_dir_trck/cb$comp_id\_former_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          $file_modifier_id_cn="$work_dir/$ctrl_dir_trck/cb$comp_id\_modifer_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          $file_oxygen_id_cn="$work_dir/$ctrl_dir_trck/cb$comp_id\_oxyg_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          $file_hydrogen_id_cn="$work_dir/$ctrl_dir_trck/cb$comp_id\_hydrg_cn_qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";
          
    #see L919      #when performing analysis for bulk model, if this model is for surface research, the upper box might be vacuum
    #see L919      #This will results in wiered CN and Qn for those atoms close to the bottom boundary because we always use periodic boundary to duplicate the structure.
    #see L919      #to resolve this issue, we may 1. set $up_w and $new_bbb same to the $zzz[top atom] or 2 set a virtual boarder which locate inside of the box around maximum interaomic distance which is similar to surface analysis
    #see L919      #although $zzz[top atom] keeps changing, it might be helpful to reduce the negative effect owing to this arbitrary setting
    #see L919      if($flg_interface==3)
    #see L919      { if($flg_vacuum==1)      #upper vacuum
    #see L919        {$lo_g=$cutoff_xyz;}
    #see L919        elsif($flg_vacuum==0)   #no vacuum
    #see L919        {$lo_g=0;}
    #see L919        elsif($flg_vacuum==-1)  #inside vacuum
    #see L919        {$lo_g=0;}              #not test
    #see L919        else
    #see L919        {;}
    #see L919      }#end if($flg_interface==3)
    #see L919      else    #has set $lo_g in advance. Search $flg_interface
    #see L919      {;}
          
        }
        if(-e $file_former_cn_NE_qn){tm::rename($file_former_cn_NE_qn);} #if file exist, rename it based on current time
        else{;}
        if(-e $file_former_cn_EQ_qn){tm::rename($file_former_cn_EQ_qn);} #if file exist, rename it based on current time
        else{;}
        if(-e $file_former_id_cn_qn){tm::rename($file_former_id_cn_qn);} #if file exist, rename it based on current time
        else{;}
        if(-e $file_modifier_id_cn){tm::rename($file_modifier_id_cn);} #if file exist, rename it based on current time
        else{;}
        if(-e $file_oxygen_id_cn){tm::rename($file_oxygen_id_cn);} #if file exist, rename it based on current time
        else{;}
        if(-e $file_hydrogen_id_cn){tm::rename($file_hydrogen_id_cn);} #if file exist, rename it based on current time
        else{;}
    
    
    
        open(FORMCNQN, ">$file_former_id_cn_qn");
        open(FORM_CN_NE_QN,">$file_former_cn_NE_qn");
        open(FORM_CN_EQ_QN,">$file_former_cn_EQ_qn");
        open(MDF_CN, ">$file_modifier_id_cn");
        open(O_CN, ">$file_oxygen_id_cn");
        open(H_CN, ">$file_hydrogen_id_cn");
        open(INI_FRM,">$file_all_spc_cn");        #CN/Qn output each atom
      }#end else of if ($flg_BL ==1)


    SETTING_CN_QN_ANALYSIS:
    ### set the initial and final index for @dirs
    # here, for CN/Qn analysis, some/all elements in @dirs will be visited
    $sampling_indx_start_dir=int($sampling_start_timestep_no/$run_no_timestep);
    $_=$sampling_start_timestep_no%$run_no_timestep;
    if($_==0 and $ctrl_starting_time_sampling>0){$sampling_indx_start_dir--;}
    $sampling_indx_end_dir=int($sampling_end_timestep_no/$run_no_timestep);$_=$sampling_end_timestep_no%$run_no_timestep;
    if($_==0 and $ctrl_ending_time_sampling>0){$sampling_indx_end_dir--;}

    #### read coordination info from dump file
    $dir_loop_i=$sampling_indx_start_dir;
 
    DIR: 
    while($dir_loop_i<=$sampling_indx_end_dir)
    {
      ### sometimes, user may want to suspend job for some reasons. Here, set a flag file STOP. 
      # When user create a file (may be empty), program will stop here. 
      # For record, the info will be written into this file for future rerun

      SUSPENSION:
      if(-e "STOP"){$_=`date`;chomp($_);system ("echo 'quit requested by user. FLG_BL=$flg_BL (1:BL analysis;0:CN/Qn),atom_id =?= $ctrl_flg_command_tgt_id\tbefore analyzing simulating directory  $dirs[$dir_loop_i] at $_' >> STOP");exit;}
      END_SUSPENSION:

      #simulation dir,like 500kstp,1mstp,1.5mstp,...
      #analysistic dir,like newzdp
      $dir=$dirs[$dir_loop_i];
      $sim_dir="$work_dir/$dir/$ctrl_anly_dir";
      $rlt_sim_dir="./$dir/$ctrl_anly_dir";
      $file="$sim_dir/$file_input_struc";
      $total_line=`wc -l < $file`;chomp $total_line;
 
 
      #read the first line of each frame
      $line=`grep -n TIMESTEP $file`;chomp($line);
      @values=split(/\r|\n/,$line);chomp(@values); #each value includes line number which will be used to extract frame in sed command
      $size_frame=$total_line/($#values+1);   #it should be integer, or data is incomplete or other error occurred
#$  _=17345.3458;
      if($size_frame=~ /\./){print "File may be incomplete. Quit.\n";$flag=0;$error_msg="$error_msg;average line # ($size_frame) in each frame is NOT integer. File may be incomplete.";die "incomplete data";}
      ##initialize variables
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
      # meanwhile, check the file whether it is complete or not
      foreach $input(@values)
      { 
        @sub_values=split(/:/,$input);chomp(@sub_values);
        $line_no[$i]=$sub_values[0];
        $i++;
      }##end foreach $input(@values)
      
      ##the last frame will not be counted if the simulating directory is not the last one owing to the last frame being the same to the first frame in the following directory
      ## However, if it is the last directory, the last frame should be counted. 
      ## To resolve such issue, here, add last_line_no+1 to @line_no, so the rest of this script does not need to change
      if($dir eq $dirs[$#dirs])
      {$tmp=`wc -l < $file`;chomp($tmp);$tmp=$tmp+1;push(@line_no,$tmp);} #$tmp is the last line # of $file, $tmp+1 is to match $last_line_frm=$line_no[$k]-1
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
      #11/13/2018 program can scan different depth from the first target atom
      if($flg_BL == 1)                        #tracking species
      {$tmp_file="$file.$target_atom_id.tmp";$indx_line_no_ini_frm=0;$indx_line_no_last_frm=$#line_no;}
      else                                    #CN/Qn distribution, set temp file, and starting and ending frame line number
      { 
        ### start from a signed directory
        $tmp_file="$file.CNQN.tmp";

        if($dir_loop_i == $sampling_indx_start_dir and $dir_loop_i == $sampling_indx_end_dir)   #data only exist in one file/dir
        {
          ### 1st index value for the 1st sampling frame
          $_="$work_dir/$dirs[$sampling_indx_start_dir]/$ctrl_anly_dir/$file_input_struc";
          $tmp=`grep -nA 1 TIMESTEP $_|grep -w '$sampling_start_timestep_no'`;
          @_=split(/-/,$tmp);
          $first_line_frm=$_[0]-1;                        #for individual frame
          $indx_line_no_ini_frm=tm::first_indx($first_line_frm,@line_no); 

          ### last index value for the last sampling frame
          $_="$work_dir/$dirs[$sampling_indx_end_dir]/$ctrl_anly_dir/$file_input_struc";
          $tmp=`grep -nA 1 TIMESTEP $_|grep -w '$sampling_end_timestep_no'`;
          @_=split(/-/,$tmp);
          $first_line_frm=$_[0]-1;
          $indx_line_no_last_frm=tm::first_indx($first_line_frm,@line_no);
        }
        else    #data cover more than one file/dir
        {  
          if($dir_loop_i == $sampling_indx_start_dir)
          {
            ### set starting line number
            $_="$work_dir/$dirs[$sampling_indx_start_dir]/$ctrl_anly_dir/$file_input_struc";
            $tmp=`grep -nA 1 TIMESTEP $_|grep -w '$sampling_start_timestep_no'`;
            @_=split(/-/,$tmp);
            $first_line_frm=$_[0]-1;                        #for individual frame
            $indx_line_no_ini_frm=tm::first_indx($first_line_frm,@line_no); 

            $indx_line_no_last_frm=$#line_no;
          }#end if($dir_loop_i == $sampling_indx_start_dir)
          elsif($dir_loop_i == $sampling_indx_end_dir)### set ending line number
          { 
            ### end by a signed directory which may be is not the same one to the starting
            $indx_line_no_ini_frm=0;

            $_="$work_dir/$dirs[$sampling_indx_end_dir]/$ctrl_anly_dir/$file_input_struc";
            $tmp=`grep -nA 1 TIMESTEP $_|grep -w '$sampling_end_timestep_no'`;
            @_=split(/-/,$tmp);
            $first_line_frm=$_[0]-1;
            $indx_line_no_last_frm=tm::first_indx($first_line_frm,@line_no);
          }#end elsif($dir_loop_i == $sampling_indx_end_dir)
          else
          { #add large limitshere
            $indx_line_no_ini_frm=0;
            $indx_line_no_last_frm=$#line_no;
          }#end else of elsif($dir_loop_i == $sampling_indx_end_dir) of if($dir_loop_i == $sampling_indx_start_dir)
        }#end else of 
      }#end else of if($flg_BL == 1)

      FRAME: 
      #for ($j=$indx_line_no_ini_frm;$j<=$indx_line_no_last_frm;$j++)  #to extract one frame, the last frame is intentionally skipped because it is the same to the first frame except for timestep=0
      for ($j=$indx_line_no_ini_frm;$j<$indx_line_no_last_frm;$j++)  #to extract one frame, the last frame is intentionally skipped because it is the same to the first frame except for timestep=0
      {
        $k=$j+1;    #to get the first line number of next frame
        #$tmp_file="$file.$target_atom_id.tmp";

        $first_line_frm=$line_no[$j];
        if($j==$#line_no){$last_line_frm=$total_line;}
        else{$last_line_frm=$line_no[$k]-1;}

        print "Extracting frame # $j from line $first_line_frm to line $last_line_frm...";
        #read one frame to a temporary file
        system("sed -n \"$first_line_frm, $last_line_frm p\" $file >$tmp_file;");#cat $tmp_file;");
        print "done\n";

        ###read all data in one frame
        open(TMP_FILE,"<$tmp_file");
        $i=0;                       #use count line # in each frame saved in *.lammptrj.tmp
        $search_i=0;                #use to control searching depth
    
        DATA: 
        while ($line=<TMP_FILE>)
        {
          $i++; 
          chomp($line);$line=tm::trim($line);
          @values=split(/\s+/,$line);chomp@values;
          if($i==1 or $i==3 or $i==5 or $i==9){next;}   #skip ITEM:...
          #elsif($i==2){$sn_time_step=$line;$sn_frame=($sn_time_step-$ctrl_starting_time_sampling)/$dump_gap+1;$frm_time=$sn_time_step*$time_step;}       #TIMESTEP or frame number
          elsif($i==2){$sn_time_step=$line;$sn_frame=$sn_time_step/$dump_gap;$frm_time=$sn_time_step* $time_step;}       #TIMESTEP or frame number
          elsif($i==4){$atm_amt=$line;}
          elsif($i==6){$aaa=$values[1]-$values[0];}
          elsif($i==7){$bbb=$values[1]-$values[0];}
          elsif($i==8){$ccc=$values[1]-$values[0];}
          else
          {#convert fractional coordinates to absolute coordinates
            $atom_id=$values[0];
            $atm_ids[$atom_id]=$atom_id;
            $atom_type[$atom_id]=$values[1];            #type
            $atom_chg[$atom_id]=$values[2];             #charge
            $xxx[$atom_id]=$aaa*$values[3];             #coordinator x
            $yyy[$atom_id]=$bbb*$values[4];             #coordinator y
            $zzz[$atom_id]=$ccc*$values[5];             #coordinator z
            
            #$flg_intf_atm: flag atoms in inteface box and extended box in different flag
            #0:out of extended box;
            #1:in interface box;
            #2:in extended box but out of interface box
            #$flg_interface 0: bulk in 3D, +1/2/3:bulk along x/y/z; -1/-2/-3: surface along x/y/z
            if($flg_interface != 0)        
            { 
              if($flg_interface==-3 or $flg_interface==3)              #extend along z direction
              {
                $new_aaa=$aaa;$new_bbb=$bbb;$new_ccc=0;   #a,b direction will be duplicated periodically, boader along c will be extended
                #mark atom in the interface box, extended box, and out of extended box
                if($zzz[$atom_id] <= $upper_threshold and $zzz[$atom_id] >= $lower_threshold)   #in the interface box only
                { 
                  $flg_intf_atm[$atom_id]=1;
                  $cnt_atm_tot_intf++;
                  $hash_key=$atom_type[$atom_id];
                  $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
                  if($atm_nm eq 'O'){$cnt_oxyg_intf++;if($atom_id <= $atm_amt_glass){$oxy_gls_intf_cnt++;}else{$oxy_wtr_intf_cnt++;}}
                  elsif($atm_nm eq 'H'){$cnt_hydg_intf++;}
                  #elsif($atm_nm eq "CA"){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
                  elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_intf++;$hash_former_intf_indv_amt{$atm_nm}++;} 
                  elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
                  else{$cnt_other_intf++;}
                }#end if($zzz[$atom_id] <= $upper_threshold and $zzz[$atom_id] >= $lower_threshold)
                elsif(($zzz[$atom_id] <= ($upper_threshold+$cutoff_xyz) and $zzz[$atom_id] > $upper_threshold) or ($zzz[$atom_id] <$lower_threshold and $zzz[$atom_id] >=($lower_threshold-$cutoff_xyz))) # in the extended box
                { 
                  $flg_intf_atm[$atom_id]=2;
                  if($flg_interface>0){;}     #do nothing for bulk analysis 
                  else
                  { 
                    $cnt_atm_tot_exbox++;
                    $hash_key=$atom_type[$atom_id];                    #atom type
                    $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
                    
                    if($atm_nm eq 'O'){$cnt_oxyg_exbox++;if($atom_id <= $atm_amt_glass){$oxy_gls_exbox_cnt++;}else{$oxy_wtr_exbox_cnt++;}}
                    elsif($atm_nm eq "H"){$cnt_hydg_exbox++;}
                    elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_exbox++;$hash_former_exbox_indv_amt{$atm_nm}++;} 
                    elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_exbox++;$hash_modf_exbox_indv_amt{$atm_nm}++;}
                    else{$cnt_other_exbox++;}
                  }#end else of if($flg_interface>0)
                }#end elsif(($zzz[$atom_id] <= ($upper_threshold+$cutoff_xyz) and $zzz[$atom_id] > $upper_threshold) or ($zzz[$atom_id] <$lower_threshold and $zzz[$atom_id] >=($lower_threshold-$cutoff_xyz)))
                else
                { $flg_intf_atm[$atom_id]=0;}
print DEBUG "\$atom_id= $atom_id\tz= $zzz[$atom_id]\t\$flg_intf_atm[$atom_id]= $flg_intf_atm[$atom_id]\n";
              }#end if($flg_interface==-3 or $flg_interface==3) 
              elsif($flg_interface==-2 or $flg_interface==2)           #extend along y direction
              {
                $new_aaa=$aaa;$new_bbb=0;$new_ccc=$ccc;   #a,c direction will be duplicated periodically, boader along b will be extended
                #mark atom in the interface box, extended box, and out of extended box
                if($yyy[$atom_id] <= $upper_threshold and $yyy[$atom_id] >= $lower_threshold)
                { $flg_intf_atm[$atom_id]=1;
                  $cnt_atm_tot_intf++;
                  $hash_key=$atom_type[$atom_id];
                  $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
                  if($atm_nm eq 'O'){$cnt_oxyg_intf++;if($atom_id <= $atm_amt_glass){$oxy_gls_intf_cnt++;}else{$oxy_wtr_intf_cnt++;}}
                  elsif($atm_nm eq 'H'){$cnt_hydg_intf++;}
                  #elsif(grep { $atm_nm eq $_ } @former_lists == 1){$cnt_former_intf++;$hash_former_intf_indv_amt{$atm_nm}++;} 
                  #elsif(grep { $atm_nm eq $_ } @modifer_lists == 1){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
                  elsif(grep { $atm_nm eq $_ } @former_lists ){$cnt_former_intf++;$hash_former_intf_indv_amt{$atm_nm}++;} 
                  elsif(grep { $atm_nm eq $_ } @modifer_lists ){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
                  else{$cnt_other_intf++;}
                }
                elsif(($yyy[$atom_id] <= ($upper_threshold+$cutoff_xyz) and $yyy[$atom_id] > $upper_threshold) or ($yyy[$atom_id] <$lower_threshold and $yyy[$atom_id] >=($lower_threshold-$cutoff_xyz)))
                { 
                  if($flg_interface>0){;}     #do nothing for bulk analysis 
                  else
                  { $flg_intf_atm[$atom_id]=2;
                    $cnt_atm_tot_exbox++;
                    $hash_key=$atom_type[$atom_id];                    #atom type
                    $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
                    if($atm_nm eq 'O'){$cnt_oxyg_exbox++;if($atom_id <= $atm_amt_glass){$oxy_gls_exbox_cnt++;}else{$oxy_wtr_exbox_cnt++;}}
                    elsif($atm_nm eq 'H'){$cnt_hydg_exbox++;}
                    elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_exbox++;$hash_former_exbox_indv_amt{$atm_nm}++;} 
                    elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_exbox++;$hash_modf_exbox_indv_amt{$atm_nm}++;}
                    else{$cnt_other_exbox++;}
                  }#end else of if($flg_interface>0)
                }
                else{$flg_intf_atm[$atom_id]=0;}
    
              }#end elsif($flg_interface==-2 or $flg_interface==2)  #extend along y direction
              elsif($flg_interface==-1 or $flg_interface==1)         #extend along x direction
              {
                $new_aaa=0;$new_bbb=$bbb;$new_ccc=$ccc;   #b,c direction will be duplicated periodically, boader along a will be extended
                #mark atom in the interface box, extended box, and out of extended box
                if($xxx[$atom_id] <= $upper_threshold and $xxx[$atom_id] >= $lower_threshold)
                { $flg_intf_atm[$atom_id]=1;
                  $cnt_atm_tot_intf++;
                  $hash_key=$atom_type[$atom_id];
                  $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
                  if($atm_nm eq 'O'){$cnt_oxyg_intf++;if($atom_id <= $atm_amt_glass){$oxy_gls_intf_cnt++;}else{$oxy_wtr_intf_cnt++;}}
                  elsif($atm_nm eq 'H'){$cnt_hydg_intf++;}
                  elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_intf++;$hash_former_intf_indv_amt{$atm_nm}++;} 
                  elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
                  else{$cnt_other_intf++;}

                }#end if($xxx[$atom_id] <= $upper_threshold and $xxx[$atom_id] >= $lower_threshold)
                elsif(($xxx[$atom_id] <= ($upper_threshold+$cutoff_xyz) and $xxx[$atom_id] > $upper_threshold) or ($xxx[$atom_id] <$lower_threshold and $xxx[$atom_id] >=($lower_threshold-$cutoff_xyz)))
                { 
                  if($flg_interface>0){;}     #do nothing for bulk analysis 
                  else
                  {               
                    $flg_intf_atm[$atom_id]=2;
                    $cnt_atm_tot_exbox++;
                    $hash_key=$atom_type[$atom_id];                    #atom type
                    $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
                    if($atm_nm eq 'O'){$cnt_oxyg_exbox++;if($atom_id <= $atm_amt_glass){$oxy_gls_exbox_cnt++;}else{$oxy_wtr_exbox_cnt++;}}
                    elsif($atm_nm eq 'H'){$cnt_hydg_exbox++;}
                    elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_exbox++;$hash_former_exbox_indv_amt{$atm_nm}++;} 
                    elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_exbox++;$hash_modf_exbox_indv_amt{$atm_nm}++;}
                    else{$cnt_other_exbox++;}
                  }#end else of if($flg_interface>0)
                }# end elsif(($xxx[$atom_id] <= ($upper_threshold+$cutoff_xyz) and $xxx[$atom_id] > $upper_threshold) or ($xxx[$atom_id] <$lower_threshold and $xxx[$atom_id] >=($lower_threshold-$cutoff_xyz)))
                else{$flg_intf_atm[$atom_id]=0;}

              }#end else of elsif($flg_interface==-1 or $flg_interface==1)  #extend along x direction
              else
              {;}
            }#end if($flg_interface != 0)
            elsif($flg_interface == 0)    #consider for bulk. not tested,01-14-2019
            {
##  # tmp pend              if($zzz[$atom_id] <= $up_w and $zzz[$atom_id] >= $lo_g)   #in the interface box only
##  # tmp pend              { $flg_intf_atm[$atom_id]=1;
##  # tmp pend                $cnt_atm_tot_intf++;
##  # tmp pend                $hash_key=$atom_type[$atom_id];
##  # tmp pend                $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
##  # tmp pend                if($atm_nm eq 'O'){$cnt_oxyg_intf++;if($atom_id <= $atm_amt_glass){$oxy_gls_intf_cnt++;}else{$oxy_wtr_intf_cnt++;}}
##  # tmp pend                elsif($atm_nm eq 'H'){$cnt_hydg_intf++;}
##  # tmp pend                #elsif($atm_nm eq "CA"){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
##  # tmp pend                elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_intf++;$hash_former_intf_indv_amt{$atm_nm}++;} 
##  # tmp pend                elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
##  # tmp pend                else{$cnt_other_intf++;}
##  # tmp pend              }#end if($zzz[$atom_id] <= $up_w and $zzz[$atom_id] >= $lo_g)
##  # tmp pend              elsif(($zzz[$atom_id] <= ($up_w+$cutoff_xyz) and $zzz[$atom_id] > $up_w) or ($zzz[$atom_id] <$lo_g and $zzz[$atom_id] >=($lo_g-$cutoff_xyz))) # in the extended box
##  # tmp pend              { $flg_intf_atm[$atom_id]=2;
##  # tmp pend                $cnt_atm_tot_exbox++;
##  # tmp pend                $hash_key=$atom_type[$atom_id];                    #atom type
##  # tmp pend                $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
##  # tmp pend                
##  # tmp pend                if($atm_nm eq 'O'){$cnt_oxyg_exbox++;if($atom_id <= $atm_amt_glass){$oxy_gls_exbox_cnt++;}else{$oxy_wtr_exbox_cnt++;}}
##  # tmp pend                elsif($atm_nm eq "H"){$cnt_hydg_exbox++;}
##  # tmp pend                elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_exbox++;$hash_former_exbox_indv_amt{$atm_nm}++;} 
##  # tmp pend                elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_exbox++;$hash_modf_exbox_indv_amt{$atm_nm}++;}
##  # tmp pend                else{$cnt_other_exbox++;}
##  # tmp pend              }#end elsif(($zzz[$atom_id] <= ($up_w+$cutoff_xyz) and $zzz[$atom_id] > $up_w) or ($zzz[$atom_id] <$lo_g and $zzz[$atom_id] >=($lo_g-$cutoff_xyz)))
##  # tmp pend              else
##  # tmp pend              { $flg_intf_atm[$atom_id]=0;}


              #### NOTE here, $up_w and $lo_g are the upper and bottom boader, namely $up_w-$lo_g=$aaa or $bbb or $ccc
              $new_aaa=$aaa;$new_bbb=$bbb;$new_ccc=$ccc;   #cell along a,b,c direction will be duplicated periodically

              #### mark atom in the interface box, extended box, and out of extended box
              $flg_intf_atm[$atom_id]=1;
              $cnt_atm_tot_intf++;
              $hash_key=$atom_type[$atom_id];
              $atm_nm=uc($hash_type_spc{$hash_key});chomp($atm_nm);
              if($atm_nm eq 'O'){$cnt_oxyg_intf++;if($atom_id <= $atm_amt_glass){$oxy_gls_intf_cnt++;                   }else{$oxy_wtr_intf_cnt++;}}
              elsif($atm_nm eq 'H'){$cnt_hydg_intf++;}
              elsif($atm_nm eq "CA"){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
              elsif(grep { $atm_nm eq $_ } @former_lists){$cnt_former_intf++;$hash_former_intf_indv_amt{$atm_nm}++;}
              elsif(grep { $atm_nm eq $_ } @modifer_lists){$cnt_modf_intf++;$hash_modf_intf_indv_amt{$atm_nm}++;}
              else{$cnt_other_intf++;}
              
              #if($yyy[$atom_id] <= $up_w and $yyy[$atom_id] >= $lo_g){$flg_intf_atm[$atom_id]=1;}
              #else{$flg_intf_atm[$atom_id]=0;}
            }#end elsif($flg_interface==0)
            else  #nothing to do
            {print "Invalid input. Quit.\n";$error_msg="$error_msg Invalid input for orientation;";$flag=0;goto MAIN;}
          }#end else of elsif.... of if($i==1 or $i==3 or $i==5 or $i==9)
        }#end while ($line=<TMP_FILE>)
        END_DATA:
#d  ie "test 1417";
        #above finish reading one frame, converting fractional coordinates to absolute values, flagging atoms which are in the interface box
        #and extended box, flagging primary target atom (here is oxygen) which is the species we are interested in, flagging the secondary target
        #(here is hydrogen) which is the neighbor of the primary target atom but it may bond to other atoms
        #below is the program search target atom and its neighbors in different level.
        #to be more general, flag is used to mark neighbor atoms at different level.
        #and a array is to used to save corresponding neighbor info, like neighbor atom ids, bond length
        
        # $flg_BL 1: BL analysis 
        #         0: CN/Qn analysis but not output all atoms in each frame, 
        #        -1: CN/Qn analysis but output all atoms in each frame, user MUST set very limited frame amounts. recommend 1 frame ONLY
        # switch between BL and CN/Qn analysis
        # here, add the initial and stop variable to control the loop
        # search level for CN/Qn is only default value= 1, user cannot change it
        # if user want to output very limited CN/Qn for all atoms in the interface box, search level value =2, user cannot change it
        # NOTE: this will cost lots of disk space and slow down the analyzing speed
        # for BL, user can define the search level 
        if($flg_BL==1)      # BL analysis is true
        {$search_atom_id=$target_atom_id;$search_loop_limit=$target_atom_id;$search_depth=$ctrl_search_depth;}
        else
        { $search_atom_id=1;
          $search_loop_limit=$atm_amt;
          
          ## here, set $flg_BL=0/-1. 0 is a switch for regular CN/Qn distribution for customized frame amounts >=2, should large to get big enough sample size
          # -1 is a switch for CN/Qn distribution for very limited frame amounts (recommend <=2). Should small enough to save disk space
          if($flg_BL==0){$search_depth=1;}
          elsif($flg_BL==-1){$search_depth=2;}
          else{;}
          
        }#end else if($flg_BL==1)      # BL analysis is true
        #elsif($flg_BL==0){$search_atom_id=1;$search_loop_limit=$atm_amt;$search_depth=1;}
        #else{$search_atom_id=1;$search_loop_limit=$atm_amt;$search_depth=2;}
#p  rint "1427 \$search_atom_id=$search_atom_id\t\$search_loop_limit=$search_loop_limit\n";$_=<STDIN>;
        ##########################################################################
        #### start BL/CN/Qn data analysis
        ##########################################################################
        while($search_atom_id<=$search_loop_limit)
        {
          # here is complicated.
          # NOTE: $search_atom_id can be unique (given by user) or all atoms. This variable is different from another $sub_atm_id in sub cal_dist. $sub_atm_id also visit all atoms, but it is used to calculate distance between atoms.
          # if calculate BL distribution, target atom id and search atom id are same as the value given by user.
          # No searching all atoms, so CN and Qn distribution can NOT be calculated
          #   in this case, target atom should be in interface box, in subroutine cal_dist to calculate the distance between all atoms. Or program will not do anything.
          # if calculate CN/Qn distribution, target atom id is temporarily, all neighbors are calculated and refined in subroutine cal_dist
          # $flg_intf_atm[$search_atom_id]    flg_BL      notation
          #             0                       0         searchingatom is not in interface box and not BL analysis, skip
          #             0                       1         target atom id given by user is out of interface box, program will get nothing output. Here, will give an error msg
          #             1                       0         no given atom id by user, CN/Qn is wanted
          #             1                       1         given atom id is in interface box and BL is wanted
          # if atom is out of interface box, will move to next one
          if($flg_intf_atm[$search_atom_id]==0 and ($flg_BL==0 or $flg_BL==-1))   #search_atom is not in the interface box and not calculate BL, skip it
          {$search_atom_id++;next;}
          else
          {
              ### reset parameters
#             @tgt_neighbor_atm_ids=();             #reset array, it will be resigned new vales in NextTarget
              @exclude_atm_ids=();                  #empty array, it will be resigned new values below
              $size_exclude_atm_ids=scalar(@exclude_atm_ids);
              @sbsdy_tgt_ngb_atm_ids=();
#p  rint "1048 \@flg_neighbor_level_",@flg_neighbor_level,"\n";$_=<STDIN>;
              @flg_neighbor_level=();

              $data_line=sprintf("FRAM_# %12d %12d(fs) ",$sn_time_step,$sn_time_step*$time_step);    #reset $data_line and set frame_sn and real time(fs)
      
              $target_atom_id=$search_atom_id;
              $tmp=$j-$indx_line_no_ini_frm+1;    #series number which show how many frames have been analyzed, esp. if the intial frame does not start from 0.
              #for intertive mode print "Calculating distance between target(",colored("$target_atom_id","bold cyan"),") and atoms in interface or extended or imaging box of ",colored("c$comp_id","bold cyan")," in no. ",colored("$tmp","bold cyan")," (frame ",colored("$sn_frame","bold magenta"),"~TIMESTEP:",colored("$sn_time_step","bold magenta"),") ",colored("$rlt_sim_dir","bold cyan"),".\n\n"; 
              print "Calculating distance between target ($target_atom_id) and atoms in interface or extended or imaging box of c$comp_id in no. $tmp (frame $sn_frame ~TIMESTEP:$sn_time_step) in $rlt_sim_dir.\n\n"; 
      
##   MAY del            ## determine location of target atom whether it is close to boarder or not
##   MAY del            ## to save calculating time
##   MAY del            # -1: extend interface box -a/b/c; +1: extend interface box +a/b/c; 0: no extention
##   MAY del            if(($xxx[$target_atom_id]-$max_cutoff)<1e-6){$flg_a=-1;}
##   MAY del            elsif(($xxx[$target_atom_id]+$max_cutoff)>=$aaa){$flg_a=1;}
##   MAY del            else{$flg_a=0;}
##   MAY del    
##   MAY del            #if($yyy[$target_atom_id]<=3){$flg_b=-1;}
##   MAY del            if(($yyy[$target_atom_id]-$max_cutoff)<1e-6){$flg_b=-1;}
##   MAY del            elsif(($yyy[$target_atom_id]+$max_cutoff)>=$bbb){$flg_b=1;}
##   MAY del            else{$flg_b=0;}
##   MAY del    
##   MAY del            if(($zzz[$target_atom_id]-$max_cutoff)<1e-6){$flg_c=-1;}
##   MAY del            elsif(($zzz[$target_atom_id]+$max_cutoff)>=$ccc){$flg_c=1;}
##   MAY del            else{$flg_c=0;} 
      
              #### calculate distance between target and neighbor atoms
              #### atoms falling in the cutoffs are save to @tgt_neighbor_atm_ids and be flagged search depth 1: 1st-depth neighbors directly bond to target atoms, 2:2nd-depth neighbors bond to the 1st-depth neighbors, 3: 3rd-level ones bonds to 2nd-level,.....
              #### corresponding info would be saved into an array for controlable output
              
              #### calculate bond length and CN of target atom
              #### and then calculate Qn which depends of neighbors CN
              ## analyze target atom only
              ## here, if CN/Qn analysis with output all atoms in interface box performed,
              ## those atoms outside box should be skipped
              push(@exclude_atm_ids,$search_atom_id);       #append searched target atomid into exclude atom list and these atoms will not be recalculated
              $flg_neighbor_level[0]=0;                     #target atom is the top level 0, only one for a specific atom id
              $search_level=$flg_neighbor_level[0];
              $line=&cal_dist($search_atom_id,$flg_intf_atm[$search_atom_id]);$line=tm::trim($line);
              #calculate CN of target atom
              $cn_no=&cn_distribution($line);chomp($cn_no);

              $tgt_cn=$cn_no;
      
              ###get total cn distribution
              ###first check atom type
              ###check atom name and save it
              ###check atom is former or oxygen or else
              ###if former, former cn plus 1
              ###if oxygen, oxygen cn plus 1
              ###else, do nothing on cn
              $hash_key=$atom_type[$search_atom_id];                    #atom type
              $tgt_nm=$hash_type_spc{$hash_key};                        #atom name, like AL,SI,CA,...
#i  f(uc($tgt_nm) eq 'H'){print "1225 H=$tgt_nm\_$search_atom_id \$flg_intf_atm[$search_atom_id]=$flg_intf_atm[$search_atom_id]\t\$cn_no=$cn_no\n";$_=<STDIN>;}
#p  rint colored("1119 ck main search_atom_id= $tgt_nm\_$search_atom_id\tcn=$cn_no\t\$flg_intf_atm[$search_atom_id]=$flg_intf_atm[$search_atom_id]\n","bold magenta");
              #if(grep(/$tgt_nm/,@former_lists))                         #atom name is in former list
              if(grep { $tgt_nm eq $_ } @former_lists)                         #atom name is in former list
              { 
#f  or($tmp=0;$tmp<=8;$tmp++){print colored("1122 tot_cn($tmp)=$hash_former_cn_tot_amt{$tmp}\ttot_cn_exbox($tmp)=$hash_former_exbox_cn_tot_amt{$tmp}\n","red");}
                $flg_former=1;
                if($flg_intf_atm[$search_atom_id]==1)                   #target former is in interface box
                {
                  $hash_former_cn_tot_amt{$cn_no}++;                    #total +1
                  $hash_former_indv_CN_cnt{$tgt_nm}{$cn_no}++;          #individual +1         
                }
                elsif($flg_intf_atm[$search_atom_id]==2)                #target former is in extended box
                {$hash_former_exbox_cn_tot_amt{$cn_no}++;$hash_former_exbox_indv_CN_cnt{$tgt_nm}{$cn_no}++;}
                else{$hash_former_cn_tot_amt{-1}++;}
#p  rint colored("1128 \$hash_former_cn_tot_amt{$cn_no}=$hash_former_cn_tot_amt{$cn_no}\t\$hash_former_exbox_cn_tot_amt{$cn_no}=$hash_former_exbox_cn_tot_amt{$cn_no}\n","bold yellow");
#f  or($tmp=0;$tmp<=8;$tmp++){print colored("1129 tot_cn($tmp)=$hash_former_cn_tot_amt{$tmp}\ttot_cn_exbox($tmp)=$hash_former_exbox_cn_tot_amt{$tmp}\n","red bold");}
#$  tmp=<STDIN>;
              }#end 
              elsif(uc($tgt_nm) eq 'O')                                 #atom name is oxygen
              { 
#f  or($tmp=0;$tmp<=8;$tmp++){print colored("1134 tot_cn($tmp)=$hash_oxygen_cn_tot_amt{$tmp}\t\$hash_oxygen_cn_glass_tot_amt($tmp)=$hash_oxygen_cn_glass_tot_amt{$tmp}\t\$hash_oxygen_cn_water_tot_amt{$tmp}=$hash_oxygen_cn_water_tot_amt{$tmp}\n","red");}
                $flg_former=0;
#                $hash_oxygen_cn_tot_amt{$cn_no}++;$flg_former=0;
                if($flg_intf_atm[$search_atom_id]==1)   #target former is in interface box
                { 
                  $hash_oxygen_cn_tot_amt{$cn_no}++;
                  if($search_atom_id <= $atm_amt_glass)
                  { $hash_oxygen_cn_glass_tot_amt{$cn_no}++;
                  }#end if($search_atom_id <= $atm_amt_glass)
                  else
                  { $hash_oxygen_cn_water_tot_amt{$cn_no}++;
                  }#end else of if($search_atom_id <= $atm_amt_glass) 
                }#end if($flg_intf_atm[$search_atom_id]==1)
                elsif($flg_intf_atm[$search_atom_id]==2)                                    #target former is in extended box
                { 
                  $hash_oxygen_cn_exbox_tot_amt{$cn_no}++;
                  if($search_atom_id <= $atm_amt_glass)
                  { $hash_oxygen_cn_glass_exbox_tot_amt{$cn_no}++;
                  }#end if($search_atom_id <= $atm_amt_glass)
                  else
                  { $hash_oxygen_cn_water_exbox_tot_amt{$cn_no}++;
                  }#end else of if($search_atom_id <= $atm_amt_glass) 
                }#endif($flg_intf_atm[$search_atom_id]==2)
                else{$hash_oxygen_cn_tot_amt{-1}++;}
#p  rint colored("1158 \$hash_oxygen_cn_tot_amt{$cn_no}=$hash_oxygen_cn_tot_amt{$cn_no}\t\$hash_oxygen_exbox_cn_tot_amt{$cn_no}=$hash_oxygen_cn_exbox_tot_amt{$cn_no}\n","bold yellow");
#f  or($tmp=0;$tmp<=8;$tmp++){print colored("1159 tot_cn($tmp)=$hash_oxygen_cn_tot_amt{$tmp}\t\$hash_oxygen_cn_glass_tot_amt($tmp)=$hash_oxygen_cn_glass_tot_amt{$tmp}\t\$ hash_oxygen_cn_glass_exbox_tot_amt{$tmp}= $hash_oxygen_cn_glass_exbox_tot_amt{$tmp}\t\$hash_oxygen_cn_water_tot_amt{$tmp}=$hash_oxygen_cn_water_tot_amt{$tmp}\t\$hash_oxygen_cn_water_exbox_tot_amt{$tmp}=$hash_oxygen_cn_water_exbox_tot_amt{$tmp}\n","red");}
#$  tmp=<STDIN>;
              }#end elsif(uc($tgt_nm) eq 'O')
              #elsif(grep(/$tgt_nm/,@modifer_lists))
              elsif(grep { $tgt_nm eq $_ } @modifer_lists)
              {
#f  or($tmp=0;$tmp<=8;$tmp++){print colored("1165 tot_cn($tmp)=$hash_modifier_cn_tot_amt{$tmp}\t\$ hash_modifier_cn_exbox_tot_amt{$tmp}= $hash_modifier_cn_exbox_tot_amt{$tmp}\n","red");}
                $flg_former=0;
                if($flg_intf_atm[$search_atom_id]==1){$hash_modifier_cn_tot_amt{$cn_no}++;}   #target former is in interface box
                elsif($flg_intf_atm[$search_atom_id]==2)                                    #target former is in extended box
                {$hash_modifier_cn_exbox_tot_amt{$cn_no}++;}
                else{$hash_modifier_cn_tot_amt{-1}++;}
#p  rint colored("1171 \$hash_modifier_cn_tot_amt{$cn_no}=$hash_modifier_cn_tot_amt{$cn_no}\t\$hash_modifier_cn_exbox_tot_amt{$cn_no}=$hash_modifier_cn_exbox_tot_amt{$cn_no}\n","bold yellow");
#f  or($tmp=0;$tmp<=8;$tmp++){print colored("1172 tot_cn($tmp)=$hash_modifier_cn_tot_amt{$tmp}\t\$ hash_modifier_cn_exbox_tot_amt{$tmp}= $hash_modifier_cn_exbox_tot_amt{$tmp}\n","red");}
#$  tmp=<STDIN>;
              }
              else        #if atom name is not one of formers or oxygen or modifier, for CN/Qn calculation, skip it; or 
              { $flg_former=-1;
                if($flg_BL<=0){$search_atom_id++;next;}
                else{;}
              }#end else of elsif(uc($tgt_nm) eq 'O') of if(grep(/$tgt_nm/,@former_lists))   
      
              $data_line="$data_line CN= $cn_no\t$line";     #here use $data_line to temporarily store return string, $data_line and $line are formatted, so no control character \t
              #if($flg_BL<0)
              #{print INI_FRM "$data_line\n";}
      
              #find neighbors and flag the search level
              #here, global array are applied and updated in the subroutine
              &NextTarget($line,$search_level);         #pass the output from substrate cal_dist to NextTarget to find the neighbor target(s)
      
              #set flag to control search level/depth
              if(scalar(@sbsdy_tgt_ngb_atm_ids) >0){$flg_search=1;}   #there are neighbor atoms and continue searching
              else{$flg_search=0;}                                    #there are no neighbor atoms and stop searching
      
              ###Qn shows whether the neighbor oxygen of a former bonds to modifer or another former
              ###For Qn(AL/SI), the maximum value is the CN 
              ###If the neighbor oxygen bonds to a modifer or H or nothing
              ###Qn--
              ###Here, initialize qn of target atom
              ###preset qn as CN if atom is a former, or qn is -10
              ###when neighbor oxgen is NBO or free one
              ###$tgt_qn--
              
              if($flg_former==1)        #current target atom is a former
              {$tgt_qn=$tgt_cn;}
              else                      #non-former
              {$tgt_qn=-10;}
      
              while($flg_search==1)
              {
                  # get the the search atom id which is the 1st atom id in the @sbsdy_tgt_ngb_atm_ids to search its neighbors and calculate its CN and Qn
                  $search_nghb_id=shift(@sbsdy_tgt_ngb_atm_ids);
                  $hash_key=$atom_type[$search_nghb_id];                    #atom type
                  $ngb_nm=$hash_type_spc{$hash_key};                        #atom name, like AL,SI,CA,...
     
                  #get the search level for the search atom
                  $search_level=shift(@flg_neighbor_level);
                  push(@exclude_atm_ids,$search_nghb_id);       #append searched target atomid into exclude atom list
#i  f($search_nghb_id==11430 or $search_nghb_id==10554){print colored("1042: \$zzz[$search_nghb_id]=$zzz[$search_nghb_id]\t\$search_level=$search_level\t\$flg_intf_atm[$search_nghb_id]=$flg_intf_atm[$search_nghb_id]\n","bold white");$tmp=<STDIN>;}
                  $line=&cal_dist($search_nghb_id,$flg_intf_atm[$search_atom_id]);$line=$line=tm::trim($line);
#p  rint "1044 \$line=$line\n";    
                  if(length($line)>0)                                               #there are neighbors
                  { 
                    $cn_no=&cn_distribution($line);chomp($cn_no);
                    
                    # to calculate qn, target must be a former, neighbor be O, CN of O <=1 (NBO OR FREE O), O be the 1st level of neighbor of target former
                    if((grep {$tgt_nm eq $_ } @former_lists) and uc($ngb_nm) eq 'O' and $cn_no <=1 and $search_level == 1)                    
                    {$tgt_qn--;}    #target is a former and NBO or free oxygen exists
                    else{;}
    #          $hash_key=$atom_type[$search_nghb_id];                    #atom type
    #          $tgt_nm=$hash_type_spc{$hash_key};                        #atom name, like AL,SI,CA,...
    #          if(grep(/$tgt_nm/,@former_lists))                         #atom name is in former list
    #          {$hash_former_cn_tot_amt{$cn_no}++;$flg_former=1;}
    #          elsif(uc($tgt_nm) eq 'O')                                 #atom name is oxygen
    #          {$hash_oxygen_cn_tot_amt{$cn_no}++;$flg_former=0;}
    #          else{$flg_former=0;next;}                                               #skip if atom name is not one of formers or oxygen
    #  print colored("953 \$flg_former=$flg_former\t\$hash_former_cn_tot_amt{$cn_no}=$hash_former_cn_tot_amt{$cn_no}\n","bold yellow");$_=<STDIN>;
      
                  }#end if(length($line)>0)
      
                  if(($search_level <= $search_depth) and (length($line) >0))            #atom is in the search range and input data is not empty
                  { 
      #print  "foreach if \$line=$line\t";
      
                    ###format control for output
                    if($search_level==1){$data_line="$data_line\n";}      #the 1st-level neighbor
                    else
                    { 
                      for($i=1;$i<=$search_level;$i++)                    #new species
                      { if($i==1){$data_line="$data_line\n";}             #new species start from a new line
                        else{$data_line="$data_line\t";}                  #insert TAB(s) based on atom's searching level
                      }#end for(my $i=1;$i<=$search_level;$i++)
                    }#end else of if($search_level==1)
     
                    $data_line="$data_line\tCN= $cn_no\t$line";             #here use $data_line to temporarily store return string
                    
                    &NextTarget($line,$search_level);                         #pass the output from substrate cal_dist to NextTarget to find the neighbor target(s)
                  }
                 
                #if($search_level >= $search_depth or scalar(@sbsdy_tgt_ngb_atm_ids) ==0)
                if(scalar(@sbsdy_tgt_ngb_atm_ids) ==0)
                {$flg_search=0;}
                else{$flg_search=1;}
       
              }#end while($flg_search==1) 
    
              # "inserted" Qn to the primary data line using replacing method
              #if(grep { $tgt_nm eq $_ } @former_lists)){$data_line =~ s/PRMRYTGT/Qn= $tgt_qn PRMRYTGT/;}
              if(grep { $tgt_nm eq $_ } @former_lists)
              { 
                $data_line =~ s/PRMRYTGT/Qn= $tgt_qn PRMRYTGT/;
              }
              #### above while loop search all neighbors
              #### calculated the bondlength between primary/subsidary target atom and other atoms
              #### calculated CN of the subsidary target atom(s)
              #### calculated Qn of the target atom
              #### here, will collect Qn of each primary target atom
              if($flg_former==1)                  #former
              { chomp($tgt_qn);
                if($flg_intf_atm[$search_atom_id]==1){$hash_former_qn_tot_amt{$tgt_qn}++;$hash_former_indv_Qn_cnt{$tgt_nm}{$tgt_qn}++;}   #target former is in interface box
                elsif($flg_intf_atm[$search_atom_id]==2)                                    #target former is in extended box
                {$hash_former_exbox_qn_tot_amt{$tgt_qn}++;$hash_former_exbox_indv_Qn_cnt{$tgt_nm}{$tgt_qn}++;}
                else{;}
              }

              #### output results to a file 
              if($flg_BL==1){print OUTPUT "$data_line\n";}
              else
              {
                if($flg_BL<0 and $flg_intf_atm[$search_atom_id]>0 )  #here only output CN/Qn for very limited frames to save disk space
               # {print INI_FRM "flg=$flg_intf_atm[$search_atom_id]\t$data_line\n";}
                {print INI_FRM "$data_line\n";}
 
                if(grep { $tgt_nm eq $_ } @former_lists)
                { 
                  ## output atom info if atom in interface box
                  ## output atom id if CN != Qn
                  ## outpput atom id if CN == Qn
                  if($flg_intf_atm[$search_atom_id] == 1)
                  {
                    print FORMCNQN "FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\tQn= $tgt_qn\n";
                    chomp($tgt_cn,$tgt_qn,$flg_intf_atm[$search_atom_id]);
                    if ($tgt_cn ne $tgt_qn)
                    { 
                      #system("echo 'FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\tQn= $tgt_qn' >> $file_former_cn_NE_qn");
                      print FORM_CN_NE_QN "FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\tQn= $tgt_qn\n";
                    }
                    elsif($tgt_cn eq $tgt_qn)    #CN=Qn
                    {
                      #system("echo 'FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\tQn= $tgt_qn' >> $file_former_cn_EQ_qn");
                      print FORM_CN_EQ_QN "FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\tQn= $tgt_qn\n";
                    }
                    else{$warn_msg="$error_msg;something unkown wrong when output former id";}
                  }#end if($flg_intf_atm[$search_atom_id] == 1)
                  else{;}
                }#end if(grep { $tgt_nm eq $_ } @former_lists)
                elsif(grep { $tgt_nm eq $_ } @modifer_lists)
                {
                  if($flg_intf_atm[$search_atom_id] == 1)
                  {
                    print MDF_CN "FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\n";
                  }
                  else{;}
                }#end elsif(grep { $tgt_nm eq $_ } @modifer_lists) of if(grep { $tgt_nm eq $_ } @former_lists)
                elsif($tgt_nm eq 'O')
                {
                  if($flg_intf_atm[$search_atom_id] == 1)
                  {
                    print O_CN "FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\n";
                  }
                  else{;}
                }
                else
                {
                  if($flg_intf_atm[$search_atom_id] == 1)
                  {
                    print H_CN "FRM $sn_frame\tTIMESTEP $sn_time_step\t$tgt_nm\_$search_atom_id\tCN= $tgt_cn\n";
                  }
                  else{;}
                }
 
              }#end else of if($flg_BL==1)
 
              $search_atom_id++;

          }#end else of if($flg_intf_atm[$search_atom_id]==0 and $flg_BL==0)

        }#end while($search_atom_id<=$search_loop_limit)  
      }#end for ($j=$indx_line_no_ini_frm;$j<$indx_line_no_last_frm;$j++)  #to extract one frame, the last frame is            intentionally skipped because it is the same to the first frame except for timestep=0
      END_FRAME:
    
      $dir_loop_i++;
    }#end while($dir_loop_i<=$sampling_indx_end_dir)
    END_DIR:
  }#end for($sampling_t_loop_i=0;$sampling_t_loop_i<$#sampling_t_lists;$sampling_t_loop_i++;)

  close(FORMCNQN);
  close(FORM_CN_NE_QN);
  close(FORM_CN_EQ_QN);
  close(MDF_CN);
  close(O_CN);
  close(H_CN);
  close(OUTPUT);

OUTPUT_CN_QN:
  ### output CN/Qn distribution
  if($flg_BL<=0)      #CN/Qn distribution
  {
    if($flg_interface>0){$file_cn_qn="$work_dir/$ctrl_dir_trck/cb$comp_id\_CN_Qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";}
    else{$file_cn_qn="$work_dir/$ctrl_dir_trck/cs$comp_id\_CN_Qn_size_$sampling_size\_TMSTP_$sampling_start_timestep_no-$sampling_end_timestep_no.dat";}
    if(-e $file_cn_qn){tm::rename($file_cn_qn);}#if file exist, rename it based on current time
    open(CN_QN,"> $file_cn_qn");
    # output header
    printf CN_QN "FRAME_NO  t(fs)  SPECIES  SAMP_SIZE  TYPE  INTF_BOX  ABS_TOT_ATM_AMT  ABS_TGT_ATM_AMT  ";
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.0f ",$cn_no;}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    { printf CN_QN "EXT_BOX  TOT_ATM_AMT_EXTBOX  AMT_ATM_EXTBOX  "; 
      for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.0f ",$cn_no;}
    }
    print  CN_QN "\n";

    ## output abs CN/Qn for former
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "FORMER    %6.0f  ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_atm_tot_intf,$cnt_former_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_cn_tot_amt{$cn_no};}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_atm_tot_exbox,$cnt_former_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_exbox_cn_tot_amt{$cn_no};}}
    print CN_QN "\n";
     
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "FORMER    %6.0f  ABS_Qn  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_atm_tot_intf,$cnt_former_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_qn_tot_amt{$cn_no};}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_atm_tot_exbox,$cnt_former_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_exbox_qn_tot_amt{$cn_no};}}
    print CN_QN "\n";
    #if there is only one former, will not output statistic info for each former
    if($#former_lists > 0)      
    {
      foreach $line (@former_lists)
      {
        if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
        printf CN_QN "$line        %6.0f  ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_former_intf,$hash_former_intf_indv_amt{$line};
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_indv_CN_cnt{$line}{$cn_no};}
        if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
        {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_atm_tot_exbox,$hash_former_exbox_indv_amt{$line};
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_exbox_indv_CN_cnt{$line}{$cn_no};}}
        print CN_QN "\n";
         
        if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
        printf CN_QN "$line        %6.0f  ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_former_intf,$hash_former_intf_indv_amt{$line};
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_indv_Qn_cnt{$line}{$cn_no};}
        if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
        {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_atm_tot_exbox,$hash_former_exbox_indv_amt{$line};
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_former_exbox_indv_Qn_cnt{$line}{$cn_no};}}
        print CN_QN "\n";
      }#end foreach $line (@former_lists)
    }#end if($#former_lists > 1)
 

    ## output CN for modifier
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "MODIFER   %6.0f  ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_atm_tot_intf,$cnt_modf_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_modifier_cn_tot_amt{$cn_no};}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_atm_tot_exbox,$cnt_modf_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_modifier_cn_exbox_tot_amt{$cn_no};}}
    print CN_QN "\n";
    
    ## output CN for oxygen 
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "OXY_TOT   %6.0f  ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_atm_tot_intf,$cnt_oxyg_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_oxygen_cn_tot_amt{$cn_no};}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_atm_tot_exbox,$cnt_oxyg_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_oxygen_cn_exbox_tot_amt{$cn_no};}}
    print CN_QN "\n";

    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "OXY_GLS   %6.0f ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_oxyg_intf,$oxy_gls_intf_cnt;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_oxygen_cn_glass_tot_amt{$cn_no};}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_oxyg_exbox,$oxy_gls_exbox_cnt;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_oxygen_cn_glass_exbox_tot_amt{$cn_no};}}
    print CN_QN "\n";

    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "OXY_WAT   %6.0f  ABS_CN  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_oxyg_intf,$oxy_wtr_intf_cnt;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_oxygen_cn_water_tot_amt{$cn_no};}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %6.0f  ",$cnt_oxyg_exbox,$oxy_gls_exbox_cnt;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",$hash_oxygen_cn_water_exbox_tot_amt{$cn_no};}}
    print CN_QN "\n";

    ## output avg CN/Qn for former
    ## here, sampling_size has NOT been used as divisor because the average species amount should have been divided by sampling size
    ## so, the sampling size was cancelled
    if($cnt_former_intf==0){$cnt_former_intf=1;}
    if($cnt_atm_tot_intf==0){$cnt_atm_tot_intf=1;}
    if($cnt_atm_tot_exbox==0){$cnt_atm_tot_exbox=1;}
    if($cnt_former_exbox==0){$cnt_former_exbox=1;}
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "FORMER    %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_atm_tot_intf/$sampling_size,100*$cnt_former_intf/$cnt_atm_tot_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_cn_tot_amt{$cn_no}/$cnt_former_intf;}
    
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_atm_tot_exbox/$sampling_size,100*$cnt_former_exbox/$cnt_atm_tot_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_exbox_cn_tot_amt{$cn_no}/$cnt_former_exbox;}}
    print CN_QN "\n";
     
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "FORMER    %6.0f  AVG_Qn  INTF_BOX  %6.0f  %6.0f  ",$sampling_size,$cnt_atm_tot_intf/$sampling_size,100*$cnt_former_intf/$cnt_atm_tot_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_qn_tot_amt{$cn_no}/$cnt_former_intf;}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_atm_tot_exbox/$sampling_size,100*$cnt_former_exbox/$cnt_atm_tot_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_exbox_qn_tot_amt{$cn_no}/$cnt_former_exbox;}}
    print CN_QN "\n";


    #if there is only one former, will not output statistic info for each former
    if($#former_lists > 0)      
    {
      foreach $line(@former_lists)
      {
        if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
        #printf CN_QN "$line       %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_atm_tot_intf,$cnt_former_intf;
        printf CN_QN "$line        %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_former_intf/$sampling_size,100*$hash_former_intf_indv_amt{$line}/$cnt_former_intf;
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_indv_CN_cnt{$line}{$cn_no}/$hash_former_intf_indv_amt{$line};}
        if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
        {#printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_atm_tot_exbox,100*$cnt_former_exbox/$sampling_size;
        printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_former_exbox/$sampling_size,100*$hash_former_exbox_indv_amt{$line}/$cnt_former_exbox;
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_exbox_indv_CN_cnt{$line}{$cn_no}/$hash_former_exbox_indv_amt{$line};}}
        print CN_QN "\n";
         
        if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
        printf CN_QN "$line        %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_former_intf/$sampling_size,100*$hash_former_intf_indv_amt{$line}/$cnt_former_intf;
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_indv_Qn_cnt{$line}{$cn_no}/$hash_former_intf_indv_amt{$line};}
        if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
        {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_former_exbox/$sampling_size,100*$hash_former_exbox_indv_amt{$line}/$cnt_former_exbox;
        for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_former_exbox_indv_Qn_cnt{$line}{$cn_no}/$hash_former_exbox_indv_amt{$line};}}
        print CN_QN "\n";
      }#end foreach $line(@former_lists)
    }#end if($#former_lists > 1)

    ## output CN for modifier
    if($cnt_modf_intf==0){$cnt_modf_intf=1;}
    if($cnt_former_intf==0){$cnt_former_intf=1;}
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "MODIFER   %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_atm_tot_intf/$sampling_size,100*$cnt_modf_intf/$cnt_atm_tot_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_modifier_cn_tot_amt{$cn_no}/$cnt_modf_intf;}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_atm_tot_exbox/$sampling_size,100*$cnt_modf_exbox/$cnt_atm_tot_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_modifier_cn_exbox_tot_amt{$cn_no}/$cnt_modf_exbox;}}
    print CN_QN "\n";
    
    ## output CN for oxygen 
    if($cnt_oxyg_intf==0){$cnt_oxyg_intf=1;}
    if($cnt_oxyg_exbox==0){$cnt_oxyg_exbox=1;}
    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "OXY_TOT   %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_atm_tot_intf/$sampling_size,100*$cnt_oxyg_intf/$cnt_atm_tot_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_oxygen_cn_tot_amt{$cn_no}/$cnt_oxyg_intf;}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_atm_tot_exbox/$sampling_size,100*$cnt_oxyg_exbox/$cnt_atm_tot_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_oxygen_cn_exbox_tot_amt{$cn_no}/$cnt_oxyg_exbox;}}
    print CN_QN "\n";

    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "OXY_GLS   %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_oxyg_intf/$sampling_size,100*$oxy_gls_intf_cnt/$cnt_oxyg_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_oxygen_cn_glass_tot_amt{$cn_no}/$cnt_oxyg_intf;}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_oxyg_exbox/$sampling_size,100*$oxy_gls_exbox_cnt/$cnt_oxyg_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_oxygen_cn_glass_exbox_tot_amt{$cn_no}/$cnt_oxyg_exbox;}}
    print CN_QN "\n";

    if ($flg_BL<0){printf CN_QN "FRAM_$sn_time_step\t$frm_time(fs)\t";}
    printf CN_QN "OXY_WAT   %6.0f  AVG_CN  INTF_BOX  %6.0f  %7.3f  ",$sampling_size,$cnt_oxyg_intf/$sampling_size,100*$oxy_wtr_intf_cnt/$cnt_oxyg_intf;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_oxygen_cn_water_tot_amt{$cn_no}/$cnt_oxyg_intf;}
    if($flg_interface<0 or ($flg_interface>0 and $flg_vacuum<=0))   #surface analysis, there might be existing extended box
    {printf CN_QN "EXT_BOX  %6.0f  %7.3f  ",$cnt_oxyg_exbox/$sampling_size,100*$oxy_wtr_exbox_cnt/$cnt_oxyg_exbox;
    for($cn_no=-1;$cn_no<=$ctrl_max_cn;$cn_no++){printf CN_QN "%7.3f ",100*$hash_oxygen_cn_water_exbox_tot_amt{$cn_no}/$cnt_oxyg_exbox;}}
    print CN_QN "\n";

    close(CN_QN);
  }#end if($flg_BL==0)
  else
  {;}

}#end if($flag==1)
else
{  
  print "Error Occured. Please check command to read the details.\n";system("tail -1 command");
}

LOG:
#achieve this operation
if($flag==1)  #log
{ system("echo '$datelog  $SCRIPT_NAME ($SCRIPT_VERSION) STATUS: $flag' >> command");   #if running this script, write it into command for record
  if($flg_BL==1)  #log
  { print "Successfully tracked $tgt_nm\_$target_atom_id. Please check $output_bondlength_file.\n"; 
    system("echo 'Successfully tracked $tgt_nm\_$target_atom_id. Please check $output_bondlength_file.'>>command");
    if(length($warn_msg)>0){system("echo '  WARNING:$warn_msg' >> command");}
  }#end if($flg_BL==1) #log
  else
  { print "Successfully analyze CN/Qn distribution in $sampling_size frames which is from $ctrl_starting_time_sampling(fs)(TIMESTEP: $sampling_start_timestep_no) to $ctrl_ending_time_sampling(fs) (TIMESTEP: $sampling_end_timestep_no) or from  Frame# $sampling_start_frame_no to $sampling_end_frame_no.\n";
    print "Created following files\n",colored("  $file_cn_qn\n","bold cyan"),", ",colored("  $file_former_cn_EQ_qn\n","bold cyan")," and ",colored("  $file_former_cn_NE_qn","bold cyan"),".\n";
    system("echo '  Successfully analyze CN/Qn distribution in $sampling_size frames which is from $ctrl_starting_time_sampling(fs)(TIMESTEP: $sampling_start_timestep_no) to $ctrl_ending_time_sampling(fs) (TIMESTEP: $sampling_end_timestep_no) or from  Frame# $sampling_start_frame_no to $sampling_end_frame_no.'>>command");
    system("echo '  Created $file_cn_qn, $file_former_cn_EQ_qn and $file_former_cn_NE_qn.' >> command");
    if(length($warn_msg)>0){system("echo '  WARNING:$warn_msg' >> command");}
  }#end else of if($flg_BL==1)  #log 
}
else
{  
  system("echo '$datelog  $SCRIPT_NAME STATUS: $flag. ERROR MSG:$error_msg ' >> command");   #if running this script, write it into command for record
  print "Error Occured. Please check logfile \'command\' to read the details.\n";system("tail -1 command");
  if(length($warn_msg)>0){system("echo '  WARNING:$warn_msg' >> command;tail -1 command;");}
}#end else of if($flag==1)  #log

CLEAN:
#in test if(-e "*.tmp"){system("rm *.tmp");}

SUBROUTINE:
################################################################################
############## subroutine or function ##########################################
SUB_CAL_DIST:
# only calculate distance between two atoms and return bond length between target and neighbor atoms
sub cal_dist      #$target_atom_id,$atom_id,target_atom_charge,atom_charge,target_x,target_y,target_z,atom_x,atom_y,atom_z,cutoff
{
  my ($sub_tgt_atm_id,$sub_flg_intf_atm)=@_;chomp ($sub_tgt_atm_id,$sub_flg_intf_atm);
  my $sub_i;my $sub_j;my $sub_k;        #index for x,y, and z
  my $sub_atm_id;                       #atom id using in subroutine                    
  my @sub_subsdry_tgt_atm_id;           #neighbors of the subsidary target atom 
  my $sub_id_indx=0;                    #index for array @sub_subsdry_tgt_atm_id
  my @sub_ddd;                          #collect all bondlength for primary and subsidary target atom in one line
  my $sub_string_output;                #all data save in one string variable
  my @sub_exclude_atm_ids;              #when atom is calculated, it will be put in this list in case duplicated calculation

#print "1165 sub cal_dist \$sub_tgt_atm_id=$sub_tgt_atm_id\n";$_=<STDIN>;  

  # set sign to tell primary target atom and subsidary atom
  if($sub_tgt_atm_id eq $target_atom_id)
  {$sub_string_output=sprintf("%8s  %8d  %5s",'PRMRYTGT',$sub_tgt_atm_id,$hash_type_spc{$atom_type[$sub_tgt_atm_id]});}
  else
  {$sub_string_output=sprintf("%8s  %8d  %5s",'SBSDRYTGT',$sub_tgt_atm_id,$hash_type_spc{$atom_type[$sub_tgt_atm_id]});}

  # if target atom is in the extended box instead of interface box self,
  # the neighbors might be missed because some neighors might be out of extended box
  # So, the label PRMRYTGT/SBSDRYTGT will be chnaged into PRMRYTGT_BD/SBSDRYTGT_BD to indicate the target atom in regarding frame is in extended box
#print "1126 \$sub_flg_intf_atm=$sub_flg_intf_atm\n";
  if($sub_flg_intf_atm == 2){$sub_string_output =~ s/TGT/TGT_BD/;}
  else{;}

  #Subroutine is used to calculate distance between target and atoms in interface and extended box
  #s1:        check "neighbor" atom is in the interface box
  #s1.1:      if no, go to next atom
  #s1.2:      if yes, check it is close to the boundary
  #s1.2.1:    if yes consider atoms in the interface box or imaging box
  #s1.2.2:    if no (not close to the boundary), directly calculate the distance using coordinates in the interface box, 
  #s1.2.1/2.1:  check the charge polarity of target and "neighbor" atom whether different
  #s1.2.1/2.2:  if yes, calculate the distance, else go to next atom
  #s1.2.1/2.3:  output the bondlength and atom id, atom type/name

  $atom_type[$sub_tgt_atm_id]=tm::trim($atom_type[$sub_tgt_atm_id]);

  #calculate distance between target atom and the rest of all other atoms
  #Here, to save calculating time, only those target atoms close to the boundary are considered to calculate the atoms in the neighbor CELL
  #No matter whether the target atom is close to boarder or not, the calculation between two atoms in the interface box will be performed
  #it is in default $flg_a,$flg_b,$flg_c=0

  #for($sub_atm_id=1;$sub_atm_id<=$#flg_intf_atm;$sub_atm_id++)
  for($sub_atm_id=$atm_amt;$sub_atm_id>=1;$sub_atm_id--)
  {  
    # Here,skipping atoms with $flg_intf_atm[$sub_atm_id]==0 can speed up the analysis
    # however, we have to consider those atoms close boarders which may bond to those atoms acrossing the boarder
    # If it happened, the skipped atom will not bond to the target atom based on below control
    # therefore, a extended box was defined and atoms in it are flagged, 
    # only atoms in the interface and extended box are used to calculate the bondlength
    if($sub_atm_id==$sub_tgt_atm_id or $atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]>0 or $flg_intf_atm[$sub_atm_id]==0){;}   #exclude target atom self or make sure two atoms have different polarity or atoms out of interface/extended box
    else
    {
      $xxx_ij=$xxx[$sub_tgt_atm_id]-$xxx[$sub_atm_id]; $xxx_ij=min(abs($xxx_ij),abs($aaa-abs($xxx_ij)));  #calculate distance between two atoms and convert it in primitive box if two atoms are close to the edge
      $yyy_ij=$yyy[$sub_tgt_atm_id]-$yyy[$sub_atm_id]; $yyy_ij=min(abs($yyy_ij),abs($bbb-abs($yyy_ij)));  #calculate distance between two atoms and convert it in primitive box if two atoms are close to the edge
      $zzz_ij=$zzz[$sub_tgt_atm_id]-$zzz[$sub_atm_id]; $zzz_ij=min(abs($zzz_ij),abs($ccc-abs($zzz_ij)));  #calculate distance between two atoms and convert it in primitive box if two atoms are close to the edge

#del test if($sub_tgt_atm_id==6189 and ($sub_atm_id==11430 or $sub_atm_id==10554)){print "1206 
#del test       \$xxx_ij=$xxx[$sub_tgt_atm_id]-$xxx[$sub_atm_id]=$xxx_ij;
#del test       \$yyy_ij=$yyy[$sub_tgt_atm_id]-$yyy[$sub_atm_id]=$yyy_ij;
#del test       \$zzz_ij=$zzz[$sub_tgt_atm_id]-$zzz[$sub_atm_id]=$zzz_ij;\n"}
#del test elsif(($sub_tgt_atm_id==11430 or $sub_tgt_atm_id==10554) and $sub_atm_id==6189)
#del test {print "1206 
#del test       \$xxx_ij=$xxx[$sub_tgt_atm_id]-$xxx[$sub_atm_id]=$xxx_ij;
#del test       \$yyy_ij=$yyy[$sub_tgt_atm_id]-$yyy[$sub_atm_id]=$yyy_ij;
#del test       \$zzz_ij=$zzz[$sub_tgt_atm_id]-$zzz[$sub_atm_id]=$zzz_ij;\n"}
#del test 
      
      #only consider target atom bond with atoms in imaging box
#      for($sub_i=0;$sub_i<=abs($flg_a);$sub_i++)
#      { 
       
#        for($sub_j=0;$sub_j<=abs($flg_b);$sub_j++)
#        {
#    
#          for($sub_k=0;$sub_k<=abs($flg_c);$sub_k++)
#          {
#
            if($atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]<0)   #different charge polarity
            {
              #$ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]=sqrt(($xxx_ij-$sub_i*$new_aaa)**2+($yyy_ij-$sub_j*$new_bbb)**2+($zzz_ij-$sub_k*$new_ccc)**2);
              $ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]=sqrt($xxx_ij**2+$yyy_ij**2+$zzz_ij**2);

              $hash_key="$atom_type[$sub_tgt_atm_id]"."-"."$atom_type[$sub_atm_id]";
              if($ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx] <= $hash_cutoff{$hash_key})
              {
                $sub_ddd[$sub_id_indx]=$ddd[$target_atom_id][$sub_atm_id][$sub_id_indx];

                chomp ($sub_tgt_atm_id,$target_atom_id);
                $_=sprintf("%8d  %5s  %.3f",$sub_atm_id,$hash_type_spc{$atom_type[$sub_atm_id]},$ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx]);
                chomp ($_,$sub_string_output);

                if(length($sub_string_output)<=0){$sub_string_output=$_;}
                else
                { 
#                  if(grep { $sub_atm_id eq $_ } @sub_exclude_atm_ids){;}       #if neighbor atom is in exclude list, do nothing because it has been calculated
#                  else{$sub_string_output="$sub_string_output\t$_";}    #if not, join two string together
                  $sub_string_output="$sub_string_output\t$_";         #if not, join two string together

                  push(@sub_exclude_atm_ids,$sub_atm_id);
                }#end else of if(length($sub_string_output)<=0)

              }#end if($ddd[$sub_tgt_atm_id][$sub_atm_id][$sub_id_indx] <= $hash_cutoff{$hash_key})

            }#end if($atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]<0)

#          }#end for($sub_k=0;$sub_k<=abs($flg_c);$sub_k++)
#        }#end for($sub_j=0;$sub_j<=abs($flg_b);$sub_j++)
#      }#end for($sub_i=0;$sub_i<=abs($flg_a);$sub_i++)


    }#end else if($sub_atm_id==$sub_tgt_atm_id or $atom_chg[$sub_tgt_atm_id]*$atom_chg[$sub_atm_id]>0 or $flg_intf_atm[$sub_atm_id]==0)

  }#end for($sub_atm_id=1;$sub_atm_id<=$#flg_intf_atm;$sub_atm_id++)

  #PERL does not support return arrays. Therefore, neighbor id and associated bondlength cannot be return in two arrays
  #To resolve this issue, here joint all data (target_id, neighbor_id, neighbor_distance) in a fixed format "primary_target_id, neighbor1_id, neighbor1_bondlength,....)
  #In addition, if the subsidary target atom does not have other neighbors except for target atom, the return value should be empty.
  $sub_string_output=tm::trim($sub_string_output);
  @_=split(/\s+/,$sub_string_output);chomp(@_);
  if (scalar(@_) ==3 and $sub_string_output=~ m/SBSDRYTGT/){$sub_string_output='';}


  $sub_string_output=tm::trim($sub_string_output);
#print colored("1139 cal_dist \$sub_string_output=$sub_string_output\n","bold yellow");
#$_=<STDIN>;
  return($sub_string_output);       #return all neighbor id and associated bond length in one line
}#end sub cal_dist

SUB_NEXTTARGET:
#substrate NextTarget is used to find neighbors' ids and target neighbors, like H or O' which is different from target O
#label each neighbors' level, like 1st, 2nd, 3rd ... to the target atom
sub NextTarget
{
  my ($nn_data_line,$nn_flg_tgt_level)=@_;$nn_data_line=tm::trim($nn_data_line);$nn_flg_tgt_level=tm::trim($nn_flg_tgt_level);
  my @nn_data_values=split(/\s+/,$nn_data_line);chomp(@nn_data_values);     #parse $nn_data_line to further get neighbor id
  my $nn_input;                   #input value in sub NextTarget
  my $nn_data_value;              #save each element from @nn_data_values
  my @nn_sbsdy_tgt_ngb_atm_ids;   #neighbor atoms' ids, will be return to the main program
  my @nn_flg_ngbs_level;          #flag those neighbors at different level close to the initial target atom

###delete  ##### line up input format ##########
###delete  #$nn_data_line may save neighbors for primary or subsidary target atom
###delete  #however, the data length is different because primary one consists of frame no while subsidary one does not have it
###delete  #e.g. 0  PRMRYTGT     13598      O     13600      H  1.003     13498      H  1.175
###delete  #        SBSDRYTGT     13498      H     12713      O  1.481
###delete  #to resove this issue, frame # would be added into the front of subsidary data
###delete  #if($nn_data_line =~ /SBSDRYTGT/){unshift(@nn_data_values,$sn_frame);}
###delete  #print "1266 \$nn_data_line=$nn_data_line\n";

  my $nn_i=0; 
  foreach $nn_data_value (@nn_data_values)
  {
    #@nn_data_values consists of target_atom_id, neighbor_atom_i_id, distance_i,....
    #1. read neighbor id as subsidary target atom id
    #2. based on setting decide to search neighbors of all/specified subsidary atom and calculate corresponding bond length
    #3. output all data to file
#print "1217 sub NextN.. \$nn_i=$nn_i\t\$nn_data_value=$nn_data_value\n";
    if($nn_i%3!=0 or $nn_data_value=~ /TGT/){$nn_i++;next;}          #skip target atom id, label, and bond length
    else  #$nn_data_value is neighbor atom id of target atom here
    {
      $nn_i++;
      if ($flg_srch_all_nghb == 0)        #only search interested elements
      {
        foreach $nn_input (@nghb_name_interested)   #check current atom/element is in interested element lists
        {
          $_=$atom_type[$nn_data_value];chomp($_);
          if ($hash_type_spc{$_} eq $nn_input)       #subsidary target atom is the interested atom/element
          {
              #if current target atom is in excluded atom ids or not
              #if in, current target atom is a parent atom id,so search next one
              #if not, push current atom id into @sbsdy_tgt_ngb_atm_ids
        #      if(grep(/^$nn_data_value$/,@exclude_atm_ids) or ($nn_flg_tgt_level == 1 and $nn_data_value == $target_atom_id)) #current target atom id is parent atom id
              #if(grep(/^$nn_data_value$/,@exclude_atm_ids)) #current target atom id is parent atom id
              if(grep { $nn_data_value eq $_ } @exclude_atm_ids) #current target atom id is parent atom id
              {next;}   #skip parent target atom(s)
              else{push(@nn_sbsdy_tgt_ngb_atm_ids,$nn_data_value);}     #add interested species id into subsidery target atom list
              push(@nn_flg_ngbs_level,($nn_flg_tgt_level+1));
          }
        }#end foreach $nn_input (@nghb_name_interested) 
      }#end if ($flg_srch_all_nghb == 0)
      else                                #scan all elements
      {
        #if(grep(/^$nn_data_value$/,@exclude_atm_ids) or grep(/^$nn_data_value$/,@sbsdy_tgt_ngb_atm_ids)) #current target atom id is parent atom id
        #if(grep(/^$nn_data_value$/,@exclude_atm_ids)) #current target atom id is parent atom id
        #if(grep(/^$nn_data_value$/,@exclude_atm_ids) or $nn_data_value == $target_atom_id) #current target atom id is parent atom id
        #if(grep(/^$nn_data_value$/,@exclude_atm_ids)) #current atom id is parent atom id
        if(grep { $nn_data_value eq $_ } @exclude_atm_ids) #current atom id is parent atom id
        {next;}   #skip parent target atom(s)
        else
        {
          #if(not (grep(/^$nn_data_value$/,@sbsdy_tgt_ngb_atm_ids)) and $nn_flg_tgt_level<$search_depth) 
          if(not (grep { $nn_data_value eq $_ } @sbsdy_tgt_ngb_atm_ids) and $nn_flg_tgt_level<$search_depth) 
          {
            push(@nn_sbsdy_tgt_ngb_atm_ids,$nn_data_value);     #add interested species id into subsidery target atom list
            push(@nn_flg_ngbs_level,($nn_flg_tgt_level+1));
          }
          else{;}
        }#end else of if(grep(/^$nn_data_value$/,@exclude_atm_ids))
      }#end else of if ($flg_srch_all_nghb == 0) 
    }#end else of if($nn_i%3!=1 or $nn_data_value=~ /TGT/)
  
  }#end foreach (@nn_data_values)

  #return values
  #here, two arrays would be returned. Function only can return one value. 
  #so, global arrays are applied
  chomp(@nn_sbsdy_tgt_ngb_atm_ids,@nn_flg_ngbs_level);
  unshift(@flg_neighbor_level,@nn_flg_ngbs_level);
  unshift(@sbsdy_tgt_ngb_atm_ids,@nn_sbsdy_tgt_ngb_atm_ids);
#my $nt_j=0;
#for($nt_j=0;$nt_j<=$#nn_flg_ngbs_level;$nt_j++)
#{print "943 sub Next.. \$nn_flg_ngbs_level[$nt_j]=$nn_flg_ngbs_level[$nt_j]\t\$nn_sbsdy_tgt_ngb_atm_ids[$nt_j]=$nn_sbsdy_tgt_ngb_atm_ids[$nt_j]\n";}
#print "\n";

#foreach (@sbsdy_tgt_ngb_atm_ids){print "946 search_level=$flg_neighbor_level[$nt_j]\t $_ is in \@sbsdy_tgt_ngb_atm_ids\n";}
#for($nt_j=0;$nt_j<=$#sbsdy_tgt_ngb_atm_ids;$nt_j++){print "946 search_level=$flg_neighbor_level[$nt_j]\t \$sbsdy_tgt_ngb_atm_ids[$nt_j]=$sbsdy_tgt_ngb_atm_ids[$nt_j]\n";}
}#end sub NextTarget

SUB_CN:
#####################################################################################################
#### $line is the information for the center atom(target and sub-target) and its 1st level neighbors
#### the data can be used to explore the CN distribution of former(s) and/or oxygen
#### if the target atom is a former, check directly bonded oxygen
#### if the target atom is an oxygen, check directly bonded former(s)
#### if the target atom is other type of atom/element, skip to next target atom
#####################################################################################################
#identify 1st level neighbors
sub cn_distribution
{ my ($cnd_line)=@_;$cnd_line=tm::trim($cnd_line);  #receive parameter
  my @cnd_values=split(/\s+/,$cnd_line);            #sparse neighbors
  my $cnd_value;                                    #save value from @cnd_values in loop
  my $cnd_tgt_atm_name;                             #target atom name
  my $cnd_tgt_atm_id;                               #target atom id
  my $cnd_ngh_atm_name;                             #neighbor atom name
  my %cnd_fmr_frq;                                  
  my $cnd_fmr_tot_frq;
  my $cnd_oxy_frq;
  my $cnd_other_frq;
  my $cnd_flg_oxyg;                                 #flag if oxygen in water molecule bonds two or more formers
  my $cnd_i;                                        #index for loop

  if($#cnd_values <3)   #no neighbors
  {
    $cnd_tgt_atm_name=uc($cnd_values[2]);
    if($cnd_tgt_atm_name eq 'O'){$cnd_fmr_tot_frq=0;}
    elsif(grep { $cnd_tgt_atm_name eq $_ } @former_lists){$cnd_fmr_tot_frq=0;}
    else{$cnd_other_frq=0;}
  }#end if($#cnd_values <3) 
  else
  {
    #check format
    if($cnd_line =~ /TGT/){;}
    #elsif($cnd_line =~ /SBSDRYTGT/)
    #{unshift(@cnd_values,$sn_frame);}
    else
    {print "ERROR!Invalid keywords in the data line.Quit!\n";$flag=0;$error_msg="$error_msg;Invalid_keyword_in_dataline";exit;}
  
    #reset variables
    foreach (@former_lists)
    {$former_cnt{$_}=0;}
    $cnd_fmr_tot_frq=0;
    $cnd_oxy_frq=0;
        
    shift(@cnd_values);                         #remove the label
    $cnd_tgt_atm_id=shift(@cnd_values);         #target atom id
    $cnd_tgt_atm_name=uc(shift(@cnd_values));   #target atom name
    $cnd_i=-1;
  
    foreach $cnd_value (@cnd_values)
    { $cnd_i++;
      if($cnd_i%3 ==1)    #neighbor atom name
      {
        $cnd_ngh_atm_name=uc($cnd_value);$cnd_ngh_atm_name=tm::trim($cnd_ngh_atm_name);   #read neighbor atom name
        if ($cnd_tgt_atm_name eq "O")                   #target atom is oxygen
        {
  
          #if(grep(/$cnd_ngh_atm_name/,@former_lists))
          if(grep {$cnd_ngh_atm_name eq $_ } @former_lists)
          {
            $cnd_fmr_tot_frq++;
            $former_cnt{$cnd_ngh_atm_name}++;
          }#end if(grep { $cnd_ngh_atm_name eq $_ } @former_lists)
          else
          {next;}#end else of if(grep { $cnd_ngh_atm_name eq $_ } @former_lists)  
  
        }#end if ($cnd_tgt_atm_name eq "O")
        elsif(grep { $cnd_tgt_atm_name eq $_ } @former_lists)  #target atom is a former
        { 
  #print "997:sub cn_distr tgt_nm=$cnd_tgt_atm_name\tnghb_nm=$cnd_ngh_atm_name\n";
          if($cnd_ngh_atm_name eq "O"){$cnd_oxy_frq++;
  #print "1002:o#=$cnd_oxy_frq\n";
  }
          else{print"Cation is not oxygen. Please double check it.\n";next;}
        }#end of elsif(grep(/$_/,@former_lists))
        else                                            #target atom is other atom except for formers and oxygen
        {$cnd_other_frq++;}#end else of elsif(grep(/$_/,@former_lists)) of if ($cnd_tgt_atm_name eq "O")
  
      }#end if($cnd_i%3 ==1)
      else{;}
    
    }#end foreach $cnd_value (@cnd_values)
  }#end else of if($cnd_other_frq<3)

  #return results in different conditions
  if($cnd_tgt_atm_name eq "O"){$_=$cnd_fmr_tot_frq;}                #target atom is O, output amout of former around it
  elsif(grep { $cnd_tgt_atm_name eq $_ } @former_lists){$_=$cnd_oxy_frq;}  #target atom is a former, output amount of oxygen around it
  else{$_=$cnd_other_frq;}                                          #none of O and former, output -1 to indicate other species

  return($_);

}#end sub cn_distribution

