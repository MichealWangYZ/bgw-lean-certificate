COMPFLAG  = -DGNU
MATHFLAG  = -DUSEFFTW3
FCPP    = cpp -C -nostdinc
F90free = /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-gfortran -ffree-form -ffree-line-length-none -fallow-argument-mismatch -std=gnu
LINK    = /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-gfortran
FOPTS   = -O2
FNOOPTS = $(FOPTS)
MOD_OPT = -J
INCFLAG = -I

CC_COMP = /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-g++ -std=c++11
C_COMP  = /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-gcc -std=c99
C_LINK  = /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-g++
C_OPTS  = -O2
C_DEBUGFLAG =

REMOVE  = /bin/rm -f

FFTWLIB      = -L/tmp/mm/root/envs/bgw/lib -lfftw3 -Wl,-rpath,/tmp/mm/root/envs/bgw/lib
FFTWINCLUDE  = /tmp/mm/root/envs/bgw/include
LAPACKLIB    = -L/tmp/mm/root/envs/bgw/lib -lopenblas -Wl,-rpath,/tmp/mm/root/envs/bgw/lib
