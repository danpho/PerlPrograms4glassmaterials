# PerlPrograms4glassmaterials

This directory is under constructing. Most programs have been done before 2020. Some programs are developping for more functions. 

All programs were written by Dr. Liaoyuan Wang. All CopyRights belong to Liaoyuan Wang.

For users' convenience, I am adding help file for each program. Please allow me to take some time.

1. Most programs were written in Perl and Python. Some ones were written in FORTRAN. FORTRAN programs were written by Dr. Alstair Cormack and his students. Based on their original programs, I debugged and developped them. Those programs have not been well organized. I would develop complete new versions and upload here.

2. All programs were run and tested on CentOS 7. If you have any questions or problems in other platforms. Please feel free to contact me at wly_ustc@hotmail.com.

3. All input files originate from LAMMPS simulation with ReaxFF. 

4. Owing to those programs would be submitted to computing nodes, input control files are required by some programs. Each program ONLY has one input control file, but may have one or more input files. User only needs to update the input control file before submitting one's job. 
One of advantages using input control file is that user can write BASH scripts to automatically update the input control files, so one can submit concurrent jobs.

5. All output files or intermediated files would be generated and saved in current or a particular directory which would be set in input control file. I strongly suggest users submit the job using slurm with command time. So you could set and get log files which provide error or output information.

6. Some tools and modules would be saved in tools and modules directories, respectively.

7. Some results were displayed in my PPT (pdf format) files. I would upload more and organize the files and folders.


I would upload more codes from the cluster after cleaning those programs (there are some tests scripts in them).



