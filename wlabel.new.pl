#!/usr/bin/perl -w
#set the strict condition;
use strict;
use warnings;#give a warning message when error occured
use diagnostics; #When you do not understand the warning message, use it to learn more info.It cost a lot of resource!
use Scalar::Util qw(looks_like_number);   #used to test numeric value. OR if ($var =~ /^[+-]?/d+/$/ ){...}
use List::MoreUtils qw(uniq);
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

my $SCRIPT_NAME=$0;   # program name
my @SPC_ORDER;        # like tuples. loop to control code which is used to identify species in a certain order, like Si-Al-O-H-Ca, if SIOH the code would be 1-0-1-1-0. It is the hash key.
$SPC_ORDER[0]='SI';
$SPC_ORDER[1]='AL';
$SPC_ORDER[2]='O';
$SPC_ORDER[3]='H';
$SPC_ORDER[4]='CA';
my $SPC;              # variable for loop

my $tmp;          # to store temprary value
my $flag=1;       # $flag=0, error occured;$flag=1, no error, program continue
my $err_msg='';   # save error message
my $wrn_msg='';   # save warning message
my $i; my $j;     # loop index
my $loop_srch_2nd_nb_i;   # loop index for searching the 2nd neighbors
my %cutoff;       # cutoff of bondlength
$cutoff{'O-H'}[2]=1.507;
$cutoff{'H-O'}[2]=1.507;
$cutoff{'O-H'}[1]=1.050;
$cutoff{'H-O'}[1]=1.050;
my $limit=($cutoff{"O-H"}[2]+$cutoff{"O-H"}[1])/2;
print "\$cutoff{'O-H'}[1]=$cutoff{'O-H'}[1]\n\$cutoff{'O-H'}[2]=$cutoff{'O-H'}[2]\n";
##$tmp=<STDIN>;

 
my $line;                     # to store line read from a file
my @values;                   # to parse each word in the $line read from a file
my @sub_values;               # same to above
my @tgt_ids;                  # to store target atom ID
my $tgt_id;                   # target atom id
my $frm_no;                   # frame number
my $frm_last_no;              # last/previous frame number
my $flg_dup;                  # flag for duplicated frames. =0, no duplication; =1 duplicated
my $frm_time_fs;              # time for related frame number with unit fs
my $frm_time;                 # time for related frame number without unit
my @frm_times;                # collect all time
my $ctrl_file='spc_list';     # control file: spc_list
my @atm_lists;                # all element listed in
my @formers;
my @anions;
my @h;
my @modifiers;
my %spc_lists_code;           # all species save in this hash table, the key is a code formed by amount of each atom in a fixed order
my @spc_lists_uniq;           # save all unique species, like Ac, Ac*,Fe, Fe*,...., used in a loop
my $hash_code_key;                 # key for hash table
my %hash_cnt_atm;             # hash table to count atom number
my $count;                    # intermediate variable to save amount of atom in a primary line
my $input_file;               # filename *_bondlength.dat
my $output_lbl_file;          # filename *_bondlength.lbl.new.dat in which all species are labelled
my $tmp_file;                 # temporary file in which one frame is saved 
my @frm_pointer;              # line no for each frame
my $frm_p_i; my $frm_p_f;     # frame pointer initial and final line number
my $frm_org_data;             # original frame data for each frame
my $frm_updt_data;            # updated frame data for each frame
my $header_input_file;        # header for the input file
my @frm_data;                 # data in one frame
my @species_data;             # data for a species which consist of all atoms, atoms IDs, and bond length between target atom and neighbors. e.g. 16652      O     16654      H  1.036      8140     CA  2.586      7319     AL  1.963
my $frm_idx_i;                # loop index only for frame
my $frm_idx_row_i;            # loop row index only for frame
my $frm_idx_col_i;            # loop col index only for frame
my @bond_h_o_tgt;             # save bond length between H and target oxygen
my @h_o_ids;                  # save atom ID of H and target oxygen, associated above array
my $ngb_id;

## define variables to calculate the lifetime and distribution in time
## define hash table which is used to count species number
my %hash_cnt_id_spc;          # count amount of species and then calculate its lifetime. key=AtomID-SpeciesName
my $hash_cnt_id_spc_key;      # hash key for hash_cnt_id_spc
my %hash_cnt_id_t;            # save labeled oxygen name at different moment
my %hash_cnt_spc_idv;         # count tot species based on each category e.g. Ac* will not be counted in Ac
my $hash_cnt_spc_idv_key;     # hash key for %hash_cnt_spc_idv
my %hash_cnt_spc_idv_t;       # count tot species based on each category e.g. Ac* will not be counted in Ac, as a function of time
#my %hash_cnt_id_spc_t;        # hash for storing species labels of an oxygen (with a fixed atomID) at different moments
my $hash_cnt_id_spc_t_key;    # key for %hash_cnt_id_spc_t
my $hash_loop_key;            # hash key using in a loop
my $hash_value;               # hash value
my %hash_cnt_id_spc_grp;      # count tot species based on group category e.g. count Ac & Ac* as the same. key=AtomID-SpeciesName
my %hash_cnt_grp_spc_t;       # count tot species based on group category e.g. count Ac & Ac* as the same, as a function of time
my $hash_cnt_grp_spc_t_key;   # hash key for %hash_cnt_grp_spc_t
my $hash_cnt_id_spc_grp_key;  # hash key for %hash_cnt_spc_tot
my %hash_cnt_spc_t;           # count spc at different moments
my $hash_cnt_spc_t_key;       # key for %hash_cnt_spc_t
my $file_id_spc_time;         # file name for species as a function of time
my $file_spc_time="spc_time_distribution.new.dat";            # file name for species as a function of time

#### collect info
## collect info for all input files
system("ls *_bondlength.dat");
$line=`ls *_bondlength.dat`;$line=tm::trim($line);
#NOTE: here, the command would generate a empty element in the very begining, the reason is unknown
# in case misleading pop up a non-element, this array will be checked one by one in the initializing loop, please see 
# initialize the hash table value for %hash_cnt_id_spc
@values=split(/\D/,$line);chomp(@values);
@tgt_ids=@values;

## collect atom type/element
if(! -e $ctrl_file)
{
  print "$ctrl_file does NOT exist. Quit.\n";
  $err_msg="$err_msg $ctrl_file does NOT exist;";
  $flag=0;
}
else
{
  #print "$ctrl_file exists.\n";
  ## in the 1st line of $ctrl_file, all elements are listed in
  $line=`head -1 $ctrl_file`;$line=tm::trim($line);
  @_=split(/#/,$line);
  @atm_lists=split(/\s+/,$_[0]);chomp(@atm_lists);
  open (SPC_LIST,"<$ctrl_file");
  $i=1;
  while($line=<SPC_LIST>)
  {
    if($i==1){$i++;next;}     #skip the first line which has been parsed before the loop
    else
    {
      $line=tm::trim(uc($line));@_=split(/#/,$line);
      @values=split(/\s+/,$_[0]);chomp(@values);
      if($i==2){@formers=@values;}
      elsif($i==3){@anions=@values;}
      elsif($i==4){@h=@values;}
      elsif($i==5){@modifiers=@values;}
      else{;}
    }
    foreach (@values){$hash_cnt_atm{$_}=0;print "\$hash_cnt_atm{$_}=$hash_cnt_atm{$_}\n";}
    $i++;
  }#end while($line=<SPC_LIST>)
}
print "All elements are ",@atm_lists,"\n";

## initialize hash table
## to efficiently identify species, all atoms are list in a fixed order, e.g. SI-AL-O-H-CA
## the related atom number will be arranged in the same order
## the value would be a key for hash table
## NOTE: make sure the key is unique!!!!!
## For CAS glasses, key shown below
#col #  grade label species     Si  Al  O   H   Ca
#8        0     Si    Si        1   0   0   0   0 
#8        0     Al    Al        0   1   0   0   0 
#8        0     Se    FreeO     0   0   1   0   0   
#8        0     H     H         0   0   0   1   0
#8        0     Ca    Ca        0   0   0   0   1
#11       1     Ar    OH        0   0   1   1   0 
#11       2     Fe    NBO       0   1   1   0   0 
#11       2     Fe    NBO       1   0   1   0   0 
#14       2     D     H2O       0   0   1   2   0 
#14       3     Ac    AlOH      0   1   1   1   0 
#14       3     La    SiOH      1   0   1   1   0 
#17       3     Ne    H3O       0   0   1   3   0 
#11       4     O     BO        0   2   1   0   0 
#11       4     O     BO        1   1   1   0   0 
#11       4     O     BO        2   0   1   0   0 
#17       4     Th    AlOH2     0   1   1   2   0 
#17       4     Ce    SiOH2     1   0   1   2   0 
#17       5     Pa    Al-OH-Al  0   2   1   1   0 
#17       5     Yb    Si-OH-Al  1   1   1   1   0 
#17       5     Pr    Si-OH-Si  2   0   1   1   0 
#17       6     Te    TBO       0   3   1   0   0 
#17       6     Te    TBO       1   2   1   0   0 
#17       6     Te    TBO       2   1   1   0   0 
#17       6     Te    TBO       3   0   1   0   0 
#
#$key=             #Si-Al-O-H-Ca

HASHTABLE:
##        SI-AL-O-H-CA
$spc_lists_code{'1-0-0-0-0'}='Si';         #Si
$spc_lists_code{'0-1-0-0-0'}='Al';         #Al
$spc_lists_code{'0-0-1-0-0'}='Se';         #free O
$spc_lists_code{'0-0-0-1-0'}='H';          #H
$spc_lists_code{'0-0-0-0-1'}='Ca';         #Ca
$spc_lists_code{'0-0-1-1-0'}='Ar';         #OH
$spc_lists_code{'0-1-1-0-0'}='Fe';         #NBO
$spc_lists_code{'1-0-1-0-0'}='Fe';         #NBO
$spc_lists_code{'0-0-1-2-0'}='D';          #H2O
$spc_lists_code{'0-1-1-1-0'}='Ac';         #AL-OH
$spc_lists_code{'1-0-1-1-0'}='La';         #SI-OH
$spc_lists_code{'0-0-1-3-0'}='Ne';         #OH3
$spc_lists_code{'2-0-1-0-0'}='O';          #SI-O-SI
$spc_lists_code{'1-1-1-0-0'}='O';          #SI-O-AL
$spc_lists_code{'0-2-1-0-0'}='O';          #AL-O-AL
$spc_lists_code{'0-1-1-2-0'}='Th';         #AL-OH2
$spc_lists_code{'1-0-1-2-0'}='Ce';         #SI-OH2
$spc_lists_code{'2-0-1-1-0'}='Pr';         #SI-OH-SI
$spc_lists_code{'1-1-1-1-0'}='Yb';         #SI-OH-AL
$spc_lists_code{'0-2-1-1-0'}='Pa';         #AL-OH-AL
$spc_lists_code{'3-0-1-0-0'}='Te';         #TBO:SI-SIO-SI
$spc_lists_code{'2-1-1-0-0'}='Te';         #TBO:SI-SIO-AL
$spc_lists_code{'1-2-1-0-0'}='Te';         #TBO:SI-OAL-AL
$spc_lists_code{'0-3-1-0-0'}='Te';         #TBO:AL-OAL-AL

$spc_lists_code{'0-0-1-1-*'}='Ar*';         #Ca nearby Ca*OH
$spc_lists_code{'0-1-1-0-*'}='Fe*';         #Ca nearby Ca*NBO
$spc_lists_code{'1-0-1-0-*'}='Fe*';         #Ca nearby Ca*NBO
$spc_lists_code{'0-0-1-2-*'}='D*';          #Ca nearby Ca*H2O
$spc_lists_code{'0-1-1-1-*'}='Ac*';         #Ca nearby Ca*AL-OH
$spc_lists_code{'1-0-1-1-*'}='La*';         #Ca nearby Ca*SI-OH
$spc_lists_code{'0-0-1-3-*'}='Ne*';         #Ca nearby Ca*OH3
$spc_lists_code{'2-0-1-0-*'}='O*';          #Ca nearby Ca*SI-O-SI
$spc_lists_code{'1-1-1-0-*'}='O*';          #Ca nearby Ca*SI-O-AL
$spc_lists_code{'0-2-1-0-*'}='O*';          #Ca nearby Ca*AL-O-AL
$spc_lists_code{'0-1-1-2-*'}='Th*';         #Ca nearby Ca*AL-OH2
$spc_lists_code{'1-0-1-2-*'}='Ce*';         #Ca nearby Ca*SI-OH2
$spc_lists_code{'2-0-1-1-*'}='Pr*';         #Ca nearby Ca*SI-OH-SI
$spc_lists_code{'1-1-1-1-*'}='Yb*';         #Ca nearby Ca*SI-OH-AL
$spc_lists_code{'0-2-1-1-*'}='Pa*';         #Ca nearby Ca*AL-OH-AL
$spc_lists_code{'3-0-1-0-*'}='Te*';         #Ca nearby Ca*TBO:SI-SIO-SI
$spc_lists_code{'2-1-1-0-*'}='Te*';         #Ca nearby Ca*TBO:SI-SIO-AL
$spc_lists_code{'1-2-1-0-*'}='Te*';         #Ca nearby Ca*TBO:SI-OAL-AL
$spc_lists_code{'0-3-1-0-*'}='Te*';         #Ca nearby Ca*TBO:AL-OAL-AL

## initialize 
## before initializing it, species name should be collected first
## above hash table shows the name of some species, like Te, are duplicated
@values=();     #reset @values
while (($hash_loop_key, $hash_value) = each (%spc_lists_code))
{ $hash_value=uc($hash_value);chomp($hash_value);
  push @values,$hash_value;         #add hash value to the end of the array
}#end while (($hash_loop_key, $hash_value) = each (%spc_lists))
@spc_lists_uniq=sort(uniq(@values));chomp(@spc_lists_uniq);              #sort and remove duplicated elements
@tgt_ids=sort(uniq(@tgt_ids));chomp(@tgt_ids);
#print "238 starts:\n";
foreach (@spc_lists_uniq){print "$_\n";}
#print "240 ends:\n";

@_=();                              #reset @_
## initialize the hash table value for %hash_cnt_id_spc
#print "241 \@values=",@tgt_ids,"===\n";$tmp=<STDIN>;
for($i=0;$i<=$#tgt_ids;$i++)
{ if(length($tgt_ids[$i])==0){;} #if element value is 0, skip it
  else
  {
    push @_,$tgt_ids[$i];           #push unempty element to @_. DO NOT DELETE THIS LINE
    chomp($tgt_ids[$i]);
#    print "\$tgt_ids[$i]=$tgt_ids[$i]\n";
    foreach $tmp (@spc_lists_uniq)
    { $tmp=uc($tmp);
      $hash_code_key="$tgt_ids[$i] - $tmp";
      $hash_cnt_id_spc{$hash_code_key}=0;
#      print"232 \$hash_cnt_id_spc{$hash_code_key}=$hash_cnt_id_spc{$hash_code_key}\n";
    }#end foreach $tmp (@spc_lists_uniq)
  }#end else of if(length($tgt_ids[$i])==0)
}#end foreach (@tgt_ids)

@tgt_ids=@_;                        #sign @tgt_ids with @_. DO NOT DELETE THIS LINE

#print "260 scalar(\@tgt_ids)=",scalar(@tgt_ids),"\$#tgt_ids=$#tgt_ids\n";
#$tmp=<STDIN>;

MAIN:
#### categorize species
## 1. identify all species: BO(O),NBO(FE),TBO(TE),OH(AR),H3O(NE),SIOH(LA),ALOH(AC),SIOH2(CE),ALOH2(TH),SI-OH-SI(PR),SI-OH-AL(YB),AL-OH-AL(PA),X-OZ-Y(SG)
##    here, each atom number will be arranged in a fixed order, so it is easy to tell what species it is using hash table

if(-e $file_spc_time){tm::rename($file_spc_time);}
open(ST,">$file_spc_time");     #species-time distribution
#output the header
print ST "time(fs)\t";
foreach(@spc_lists_uniq) 
{print ST "$_\t";}
print ST "\n";

######################################## loop structures #############################################
# CHECK CODE
# foreach (@tgt_ids)
# { if target is not oxygen
#   else  # target is oxygen
#   { for loop, extract frame data
#     {  
#       foreach (@SPC_ORDER)  #fixed atom order which is used to set a unique code to identify species
#       { if H exist
#         {
#          if (O-H) hydrogen bond => get code for species, like 0-0-1-1-0 Ar, 0-0-1-1-* Ar*(Ca nearby) 
#         }  
#       }#end foreach (@SPC_ORDER)
#       count species number based on different rules/standards
#     }# end for loop, extract frame data
#   }#end else of if target is not oxygen
# }#end foreach (@tgt_ids)
####################################### end loop structure ###########################################

#$_='11118';
#$_='16652';
#$_='10036';
#$tgt_id=$_;
START_SCAN:
foreach $tgt_id (@tgt_ids)
{
  $input_file="$tgt_id\_bondlength.dat";
  $tmp_file="$tgt_id\_bondlength.lbl.tmp";
  $output_lbl_file="$tgt_id\_bondlength.lbl.new.dat";
  $line=`grep -n FRAM $input_file`;chomp($line);
  @values=split(/:|\r|\n/,$line);chomp(@values);
  @frm_pointer=@values;             # initial line no for each frame, and the 1st line of each frame
#print "207 \$frm_pointer[0]=$frm_pointer[0]\t\$frm_pointer[1]=$frm_pointer[1]\n";#$tmp=<STDIN>;

  ## tell target atom is oxygen or not
  ## if O is the target atom, species need to be identified
  ## if not, currently nothing to do
  @_=split(/\s+/,$frm_pointer[1]);chomp(@_);    # parse the first data line to see the target atom in $_[7]
  #if(!$frm_pointer[1] =~ /$tgt_id\s+O/)       # target is not oxygen
  if(uc($_[7]) ne 'O')
  { print "$tgt_id is not oxygen. Skip scanning this target atom.\n";
    $wrn_msg="$wrn_msg$tgt_id is $_[7] instead of oxygen,skip this target atom $tgt_id;";
  }#end if(uc($_[7] ne 'O') ##if(!$frm_pointer[1] =~ /$tgt_id\s+O/)
  else                                        # target is oxygen
  {
    print "Target atom (ID:$tgt_id) is $_[7]\_$tgt_id.\n";

    open (FRM_DATA,">$output_lbl_file");
    ## get the header 
    $header_input_file=`head -1 $input_file`;chomp($header_input_file); #save header from $input_file
    ## save file header to new file $output_lbl_file
#    print FRM_DATA "$header_input_file\n";

    ## extract frame data
    for($frm_idx_i=0;$frm_idx_i<$#frm_pointer;$frm_idx_i=$frm_idx_i+2) #Here, +2 because each data line is splited into two arrays and joined together
    {
#print "333 \$frm_idx_i=$frm_idx_i\t\$#frm_pointer=$#frm_pointer\n";$tmp=<STDIN>;
#print "334 $frm_pointer[$frm_idx_i]\n";
      ## read frame initial and final line number
      $frm_p_i=$frm_pointer[$frm_idx_i];        #first line for a frame
      if(($frm_idx_i+2)>$#frm_pointer)
      {$frm_p_f="\$";}
      else{$frm_p_f=$frm_pointer[$frm_idx_i+2]-1;}    #last line for a frame
#print "340 \$frm_p_i=$frm_p_i\t\$frm_p_f=$frm_p_f\n";
      
      EXTRACT_FRAME_AND_ANALYSIS:
      ## read one frame data
      $line=`sed -n '$frm_p_i, $frm_p_f p' $input_file`;chomp($line);
      $frm_org_data=$line;                      #original frame data 
      ## get each line as an element in an array @frm_data
      @frm_data=split(/\r|\n/,$line);
      #@frm_data=grep(s/\s*$//g,@values);   #each element is one line of frame data, remove all white space in the beginning and end of a line/element
      s{^\s+|\s+$}{}g foreach @frm_data;    #remove white spaces in the beginning & ending of each element which is one line of frame
      
      ##remove first six columns in case keywords consist of element name
      @species_data=split(/TGT/,$frm_data[0]);
      #@species_data=grep(s/\s*$//g,@_);      #remove white spaces at the beginning and end of each element
      s{^\s+|\s+$}{}g foreach @species_data;  #remove white spaces at the beginning and end of each element

      @sub_values=split(/\s+/,$frm_data[0]);chomp(@_);    #parse PRMRYTGT line
      $frm_no=$sub_values[1];                             #frame number

      VERIFY_DUPLICATION:
      ## data might have duplicated ones owing to the bug in previous program wcnqn.auto.pl?
      ## To avoid duplicated counting, here, current frame number and previous frame number need to be compared each other
      if(!$frm_last_no){$frm_last_no=$frm_no;$flg_dup=0;}            #if $frm_last_no is unsigned, set it same as $frm_no
      else
      {
#print "361 defined last=$frm_last_no\tcurrent=$frm_no\n";$_=<STDIN>;
        if($frm_last_no == $frm_no){$flg_dup=1;next;}    #duplicated frame data, skip to next frame
        else  # no duplicated frame data
        {$flg_dup=0;$frm_last_no=$frm_no;}
      }#end else of if(!$frm_last_no)
      
      if($flg_dup==0)       #not duplicated btw current and previous frame data
      {
          $frm_time_fs=$sub_values[2];                        #time for related frame number with unit fs
          $frm_time=$frm_time_fs;                             #pass time with unit to another variable to remove the unit
          $frm_time =~ s/\D+//g;                              #time only without unit, here, the equation is to remove non-digit char
          push @frm_times,$frm_time;                          #push time for each frame into @frm_times 
          print "Searching frame $frm_no (time: $frm_time_fs) from line  $frm_p_i to $frm_p_f in $input_file.\n";
    
          ## here, $frm_data[0] is the primary line which show all atoms surrounded target atom
          # reset %hash_cnt_atm
          %hash_cnt_atm = ();
          
          CODING:
          ## count atomic number based on above fixed order to get the hash key (unique code) which is used to get species name
          ## to realize this, count atom number using a loop which is visited in Si-Al-O-H-Ca order 
          #i.e. Si-Al-O-H-Ca 0-1-1-2-* AlOH2 nearby Ca
          #0-1-1-2-0 AlOH2 no Ca nearby
          $hash_code_key='';     #reset hash key
          foreach $SPC (@SPC_ORDER)    #arrange the atom number in a fixed order
          {
            INITIAL_CODE: 
            ## count how many atoms around the target atoms
            $SPC=tm::trim(uc($SPC));
            $count = () = uc($species_data[$#species_data]) =~ /$SPC/g;     #count atom amount in primary line
            $hash_cnt_atm{$SPC}=$count;                     #save amount to harsh table
#:/474    print "380 \$hash_cnt_atm{$SPC}=$hash_cnt_atm{$SPC}\n";
    
    #print "365 \$frm_data[0]=$frm_data[0]\n[1]=$frm_data[1]\n\$species_data[$#species_data]=$species_data[$#species_data]\n===end 267\n";#$tmp=<STDIN>;
            CODE_CORRECTION:
            ## "degrade" species into one without hydrogen bond
            ## if O-H is close to 1.5, O-H is hydrogen bond
    ####        if($species_data[$#species_data] =~ /H/ and $SPC eq 'H')          #check H exist,@species_data has two elements splited by TGT
    ####        { 
            ## target oxygen may bond with H which might also bond with another oxygen, may not
            ## first check the O-H bond between target oxygen and H,
            ## second check the O-H bond between H and another oxygen if this bond exist
    #print"274 $species_data[$#species_data]\n 264: \$#sub_values=$#sub_values\n";
            for($i=9;$i<=$#sub_values;$i = $i+3)                #search atom from the 10th coloumn
            {
    #print "395 \$i=$i\t\$sub_values[$i]=$sub_values[$i]\n";
              ## to judge whether O-H is hydrogen bond or not
              ## if atom is H, get its id $sub_values[$i-1] and bondlength $sub_values[$i+1]
              if($sub_values[$i] eq 'H')
              {
                $ngb_id=$sub_values[$i-1];
                ## check hydrogen bond between target oxygen and H
                ## if O-H is true, check whether H bonds with another oxygen
                ##  if H-O', output warning, it might be unusual 
                ##  else, output
                if($sub_values[$i+1] <= ($cutoff{'O-H'}[1]+$cutoff{'O-H'}[2])/2)    #NOT hydrogen bond btw H-O(tgt), need to consider 2nd neighbors
                {
                  #push @bond_h_o_tgt, $_[$j+1];push @h_o_ids, $_[$j-1];             # save bond length between H(s) and target oxygen
                  ## check whether H is shared by another oxygen
                  for($frm_idx_row_i=1;$frm_idx_row_i<=$#frm_data;$frm_idx_row_i++)
                  {
                    ###????  where to put? attention loops!
                    ## suggest scan all atoms and then search the frame data
                    if($frm_data[$frm_idx_row_i] =~ /SBSDRYTGT\s+$ngb_id\s+$_/)    #SBSDRYTGT line has target neighbor atom id
                    {
                      @_=split(/\s+/,$frm_data[$frm_idx_row_i]);chomp(@_);
                      for($loop_srch_2nd_nb_i=6;$loop_srch_2nd_nb_i<=$#_;$loop_srch_2nd_nb_i = $loop_srch_2nd_nb_i +3)
                      {
                        if(uc($_[$loop_srch_2nd_nb_i]) eq 'O' and $_[$loop_srch_2nd_nb_i-1] == $tgt_id)  #bond with target oxygen, skip
                        {next;}
                        else      #bond with another oxygen
                        {
                          if($_[$loop_srch_2nd_nb_i+1] <= ($cutoff{'O-H'}[1]+$cutoff{'O-H'}[2])/2) # O-H bond with 2nd ngb O 
                          {
                            ## H bond with two Os and two O-H formed
                            ## it is unusal in glass. This is water sharing one H with O in glass
                            ## need to create warning message
                            $hash_cnt_atm{$_}--;
                            $wrn_msg="$wrn_msg"."unusual bond between H($ngb_id) and target O($tgt_id), neighbor O($_[$loop_srch_2nd_nb_i-1]) in frame $frm_no;";
                            print "$wrn_msg\n";
                          }#end if($_[$loop_srch_2nd_nb_i+1]) <= ($cutoff{'O-H'}[1]+$cutoff{'O-H'}[2])/2)
                          else    # hydrogen bond with another oxygen
                          {
                            ;
                          }#end else if($_[$loop_srch_2nd_nb_i+1]) <= ($cutoff{'O-H'}[1]+$cutoff{'O-H'}[2])/2)
                        }#end else of if(uc($_[$loop_srch_2nd_nb_i]) eq 'O' and $_[$loop_srch_2nd_nb_i-1] == $tgt_id)
                      }#end for(my $loop_srch_2nd_nb_i=6;$loop_srch_2nd_nb_i<=$#_;$loop_srch_2nd_nb_i = $loop_srch_2nd_nb_i +3)
                    }#end if($frm_data[$frm_idx_row_i] =~ /$ngb_id/)
                    else
                    {;}
                  }#end for($frm_idx_row_i=1;$frm_idx_row_i<=$#frm_data;$frm_idx_row_i++)               
                }#end if($sub_values[$i+1] <= ($cutoff{'O-H'}[1]+$cutoff{'O-H'}[2])/2)    #NOT hydrogen bond
                else      #hydrogen bond, minus one for amount of H bonded to target oxygen. do not need to consider 2nd neighbors
                {$hash_cnt_atm{'H'}--;}
    
              }#end if($sub_values[$i] eq 'H')
              else{;}
            }#end for($i=9;$i<=$#sub_values;$i++)
    
            ## if there is existing Ca nearby, species would be mark a "*" to get attention
            if(uc($SPC) ne 'CA')        #no Ca nearby
            { if(length($hash_code_key)==0){$hash_code_key="$hash_cnt_atm{$SPC}";}
              else{$hash_code_key="$hash_code_key-$hash_cnt_atm{$SPC}";}
            }#end if($SPC ne 'CA')
            else                  #Ca nearby
            { 
#print "474 \$hash_code_key=$hash_code_key\n";$_=<STDIN>;
              if(length($hash_code_key)==0)
              #if()
              { 
                if($hash_cnt_atm{'CA'} >0){$hash_code_key="*";}
                else{$hash_code_key="0";}
              }#end if(length($hash_code_key)==0)
              else
              {
                if($hash_cnt_atm{'CA'} >0){$hash_code_key="$hash_code_key-*";}
                else{$hash_code_key="$hash_code_key-0";}
              }#end else of if(length($hash_code_key)==0)
            }#end else if(uc($SPC) ne 'CA')
            END_CODE_CORRECTION:
          }#end foreach (@SPC_ORDER)
          END_CODING:
          print "Species Code = $hash_code_key\t";
          if($spc_lists_code{$hash_code_key})     #$spc_lists_code{$hash_code_key} exist
          {print "Species Name = $spc_lists_code{$hash_code_key}\n";}
          else  #$spc_lists_code{$hash_code_key} does NOT exist
          {print "Species Name = NA/ERROR\n";}
         
          VERIFYING_CODE:
          #test $hash_code_key="1-2-3-2-9";
          if(!$spc_lists_code{$hash_code_key}) #invalid code
          { $err_msg="$err_msg"."hash code ($hash_code_key) does NOT exist! Check the structure in $tgt_id\_bondlength.dat \@ frame_no=$frm_no(time=$frm_time_fs) or hash table %spc_lists_code in this program;\n";
            print "Error occured. hash code ($hash_code_key) does NOT exist! Check the structure in $tgt_id\_bondlength.dat \@ frame_no=$frm_no(time=$frm_time_fs) or hash table %spc_lists_code in this program;\n";
          }#end if(!$spc_lists_code{$hash_code_key})  # invalid code
          else    # valid code
          {
            ## replace the target oxygen with a species name
            $frm_updt_data=$frm_org_data;
            $_=$spc_lists_code{$hash_code_key};
            #$frm_updt_data =~ s/PRMRYTGT\s+$tgt_id\s+O/PRMRYTGT\t$tgt_id\t$spc_lists_code{$hash_code_key}/g;
            if($frm_updt_data =~ /PRMRYTGT_BD/)
            {$frm_updt_data =~ s/PRMRYTGT_BD\s+$tgt_id\s+O/PRMRYTGT_BD\t$tgt_id\t$_/g;}
            else
            {$frm_updt_data =~ s/PRMRYTGT\s+$tgt_id\s+O/PRMRYTGT\t$tgt_id\t$_/g;}
     
            ## output the searched and labeled data into a new label file
#            print FRM_DATA "$frm_updt_data\n";
                  
            ## count species number to calculate its lifetime or see its distribution as a function of time
      
            ## 1. lifetime for a specific target oxygen
            ## count all species which can be identified each other, e.g. Ac # Ac*
            $hash_cnt_id_spc_key="$tgt_id - ".uc($spc_lists_code{$hash_code_key});  # hash_code_key="atmID - spc", e.g. "16652 - AC"
            if($hash_cnt_id_spc{$hash_cnt_id_spc_key})   # $hash_cnt_id_spc{$hash_cnt_id_spc_key} has been initialized or has a value
            { $hash_cnt_id_spc{$hash_cnt_id_spc_key}++;}
            else                                         # $hash_cnt_id_spc($hash_cnt_id_spc_key} has not been initialized
            {$hash_cnt_id_spc{$hash_cnt_id_spc_key}=1;}
      
            ## count all grouped species, e.g. Ac=Ac*
            $tmp=uc($spc_lists_code{$hash_code_key}); 
      
            $tmp =~ s/\*//g;$tmp=tm::trim($tmp);
#print "507:",uc($spc_lists_code{$hash_code_key}),"\tgrp_spc=$tmp\n";
            $hash_cnt_id_spc_grp_key="$tgt_id - $tmp";   # atomID - GroupSpecies, e.g. "10036 - AC"
            $hash_cnt_grp_spc_t_key=$tmp;
            if($hash_cnt_id_spc_grp{$hash_cnt_id_spc_grp_key})
            { $hash_cnt_id_spc_grp{$hash_cnt_id_spc_grp_key}++;}
            else
            { $hash_cnt_id_spc_grp{$hash_cnt_id_spc_grp_key}=1;}
      
            # save label at different moments
            $hash_cnt_id_t{$tgt_id}[$frm_time] = $hash_cnt_spc_t_key = uc($spc_lists_code{$hash_code_key});
#print "489 \$hash_cnt_id_spc{$hash_cnt_id_spc_key}=$hash_cnt_id_spc{$hash_cnt_id_spc_key}\$hash_cnt_id_t{$tgt_id}[$frm_time]=$hash_cnt_id_t{$tgt_id}[$frm_time]\n\n";
                  
            ## 4. species amount as a function of time
            if($hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]){$hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]++;}
            else{$hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]=1;}
            if($hash_cnt_grp_spc_t{$hash_cnt_grp_spc_t_key}[$frm_time]){$hash_cnt_grp_spc_t{$hash_cnt_grp_spc_t_key}[$frm_time]++;}
            else{$hash_cnt_grp_spc_t{$hash_cnt_grp_spc_t_key}[$frm_time]=1;}
#print "541 \$hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]=$hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]\n";$_=<STDIN>;
#print "542 \$hash_cnt_grp_spc_t{$hash_cnt_grp_spc_t_key}[$frm_time]=$hash_cnt_grp_spc_t{$hash_cnt_grp_spc_t_key}[$frm_time]\n";$_=<STDIN>;
      #      ## 2. lifetime for a specific species individually and as a function of time
      #      $hash_cnt_spc_idv_key=uc($spc_lists_code{$hash_code_key});                      # i.e. Ac is different from Ac*
      #      #$hash_cnt_id_spc_idv{$hash_cnt_spc_idv_key} = $hash_cnt_id_spc_idv{$hash_cnt_spc_idv_key}++ // 1;
      #      if($hash_cnt_spc_idv{$hash_cnt_spc_idv_key}){$hash_cnt_spc_idv{$hash_cnt_spc_idv_key}++;}
      #      else{$hash_cnt_spc_idv{$hash_cnt_spc_idv_key}=1;}
      #      if($hash_cnt_spc_idv_t{$hash_cnt_spc_idv_key}[$frm_time]){$hash_cnt_spc_idv_t{$hash_cnt_spc_idv_key}[$frm_time]++;}
      #      else{$hash_cnt_spc_idv_t{$hash_cnt_spc_idv_key}[$frm_time]=1;}
      #print "466 \$hash_cnt_spc_idv{$hash_cnt_spc_idv_key}=$hash_cnt_spc_idv{$hash_cnt_spc_idv_key}\n";
      #
      #      ## 3. lifetime for a specific species group, like Ac and Ac* being in a same group, and as a function of time
      #      @_=split(/\*/,uc($spc_lists_code{$hash_code_key}));chomp(@_);
      #      $hash_cnt_id_spc_tot_key=$_[0];                                             # i.e. Ac and Ac* are same
      #      #$hash_cnt_id_spc_tot_key=uc($spc_lists_code{$hash_code_key});
      #      if($hash_cnt_id_spc_tot{$hash_cnt_id_spc_tot_key}){$hash_cnt_id_spc_tot{$hash_cnt_id_spc_tot_key}++;}
      #      else{$hash_cnt_id_spc_tot{$hash_cnt_id_spc_tot_key}=1;}
      #      if($hash_cnt_spc_tot_t{$hash_cnt_id_spc_tot_key}[$frm_time]){$hash_cnt_spc_tot_t{$hash_cnt_id_spc_tot_key}[$frm_time]++;}
      #      else{$hash_cnt_spc_tot_t{$hash_cnt_id_spc_tot_key}[$frm_time]=1;}
      #      print "476 \$hash_cnt_id_spc_tot_key=$hash_cnt_id_spc_tot_key\t\$hash_cnt_spc_tot_t{$hash_cnt_id_spc_tot_key}[$frm_time]=$hash_cnt_spc_tot_t{$hash_cnt_id_spc_tot_key}[$frm_time]\$hash_cnt_id_spc_tot{$hash_cnt_id_spc_tot_key}=$hash_cnt_id_spc_tot{$hash_cnt_id_spc_tot_key}\n";$tmp=<STDIN>;
      #
             
          }#end else if(!$spc_lists_code{$hash_code_key}) #valid code
          
      }#end else of if(!$frm_last_no)
    }#end for(my =0;$frm_idx_i<=$#frm_pointer;$frm_idx_i+=2) #extract frame data
   
  }#end else of if (uc($_[7]) ne 'O')#if(!$frm_pointer[1] =~ /$tgt_id\s+O/) # check target atom is oxygen or not
}#end foreach $SPC (@tgt_ids)  # search all listed atom id(s)

my $spc_nm;
open (SPC_LIFE,">spc_life.new.dat");
## output header
print SPC_LIFE "AtomID";
foreach $spc_nm (@spc_lists_uniq)
{print SPC_LIFE "\tt($spc_nm)(fs)";}
print SPC_LIFE "\n";
## collect counting info
foreach $tgt_id (@tgt_ids)
{
  print SPC_LIFE "$tgt_id";
  foreach $spc_nm (@spc_lists_uniq)
  {
    $hash_cnt_id_spc_key="$tgt_id - $spc_nm";         # hash_code_key="atmID - spc", e.g. "16652 - AC"
    print SPC_LIFE "\t$hash_cnt_id_spc{$hash_cnt_id_spc_key}";
  }#end foreach $spc_nm (@spc_lists_uniq)
  print SPC_LIFE "\n";
}#end foreach $line (@tgt_ids)


## 4. species amount as a function of time
foreach $frm_time (@frm_times)
{
  print ST "$frm_time\t";            #print frame time
  print  "$frm_time\t";            #print frame time
  foreach $hash_cnt_spc_t_key (@spc_lists_uniq)
  { 
    if($hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time])       # hash value exists
    { print ST "$hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]\t";
      print  "$hash_cnt_spc_t{$hash_cnt_spc_t_key}[$frm_time]\t";
    }
    else    # hash value does NOT exist
    { print ST "0\t";
      print "0\t";
    }
  }#end foreach my $spc (@spc_lists_uniq)
  print ST "\n";
  print  "\n";
}#end foreach my $t (@frm_times)

## clean intermediate files
if (-e $tmp_file){system("rm $tmp_file");}

## write commands to command file for record
my $datelog=`date`;
$datelog=tm::trim($datelog);
system("echo '$datelog  $SCRIPT_NAME STATUS $flag' >> command");   #if running this script, write it into command for record


sub trim 
{
my ($sub_line)=@_;
chomp($sub_line);
$sub_line=~s/^\s+|\s+$//g;
return $sub_line;
}
