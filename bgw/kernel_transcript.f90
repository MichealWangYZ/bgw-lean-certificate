! Restricted transcription of the arithmetic of the occupied and unoccupied
! branches of `sigma_gpp_cpu`, BerkeleyGW 4.0, Sigma/mtxel_cor.f90.
!
!   tarball sha256 1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49
!   mtxel_cor.f90 sha256 8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd
!
! This is NOT BerkeleyGW. It is a standalone program that reuses the executable
! statements of the real-flavor CPU kernel (lines 1810-1848 for the occupied
! branch, 1879-1897 for the unoccupied branch) with the same declared types, so
! that the branch selection and the binary64 evaluation can be observed without
! a full electronic-structure run. Everything outside those statements --- the
! G/G' loops, matrix elements, Coulomb factors, MPI/OpenMP --- is removed.
!
! Declared types are taken from the subroutine headers:
!   SCALAR (= real(DP) with flavor_real.mk) :: Omega2, wtilde2, ssx, sch
!   complex(DPC)                            :: wtilde, delw, wdiff, cden
!   real(DP)                                :: delwr, wdiffr, rden, wxt, ssxcutoff
! The complex-to-real assignments `wtilde2 = wtilde**2` and `sch = delw*I_eps`
! are the source's own; they are reproduced, not repaired.

program kernel_transcript
  implicit none
  integer,  parameter :: DP  = kind(1.0d0)
  integer,  parameter :: DPC = kind((1.0d0,1.0d0))

  ! Common/nrtype.f90 lines 161-162, 155
  real(DP), parameter :: TOL_Small = 1.0d-6
  real(DP), parameter :: TOL_Zero  = 1.0d-12
  real(DP), parameter :: RYD       = 13.60569253d0
  ! Sigma/inread.f90 lines 151-152 (defaults for `gpp_broadening`, `gpp_sexcutoff`)
  real(DP), parameter :: sig_gamma  = 0.5d0
  real(DP), parameter :: sig_sexcut = 4.0d0

  real(DP) :: limitone, limittwo
  real(DP) :: I_eps, wxt, delwr, wdiffr, rden, ssxcutoff
  real(DP) :: Omega2, wtilde2, ssx, sch
  complex(DPC) :: wtilde, delw, wdiff, cden
  real(DP) :: occupied, empty, offset
  integer  :: i, branch

  ! mtxel_cor.f90 lines 1698-1699
  limitone = 1D0/(TOL_Small*4D0)
  limittwo = sig_gamma**2

  I_eps  = 1.0d0
  wtilde = cmplx(1.0d0, 0.0d0, kind=DPC)

  write(*,'(a)') '# BerkeleyGW 4.0 sigma_gpp_cpu arithmetic, real flavor'
  write(*,'(a,es23.16)') '# I_eps    = ', I_eps
  write(*,'(a,es23.16)') '# wtilde   = ', real(wtilde, DP)
  write(*,'(a,es23.16)') '# limitone = ', limitone
  write(*,'(a,es23.16)') '# limittwo = ', limittwo
  write(*,'(a,es23.16)') '# RYD      = ', RYD
  ! ssx, sch, occupied and empty are dimensionless; the energy dimension of
  ! Sigma is carried by vcoul, which is not part of this kernel.
  write(*,'(a)') '# offset wxt branch sch ssx occupied empty occupied_times_RYD'

  do i = 1, 17
     offset = 10.0d0**(-dble(i-1)/2.0d0)
     wxt = real(wtilde, DP) + offset

     ! ---- mtxel_cor.f90 line 1746: wx clamped away from zero -----------------
     if (abs(wxt) .lt. TOL_Zero) wxt = TOL_Zero

     ! ---- mtxel_cor.f90 lines 1810-1848, verbatim ---------------------------
     wtilde2 = wtilde**2
     Omega2 = wtilde2 * I_eps

     wdiff = wxt - wtilde

     cden = wdiff
     rden = cden * CONJG(cden)
     rden = 1D0 / rden
     delw = wtilde * CONJG(cden) * rden
     delwr = delw*CONJG(delw)
     wdiffr = wdiff*CONJG(wdiff)

     if (wdiffr.gt.limittwo .and. delwr.lt.limitone) then
       branch = 1
       sch = delw * I_eps
       cden = wxt**2 - wtilde2
       rden = cden*CONJG(cden)
       rden = 1D0 / rden
       ssx = Omega2 * CONJG(cden) * rden
     else if ( delwr .gt. TOL_Zero) then
       branch = 2
       sch = 0.0d0
       cden = (4.0d0 * wtilde2 * (delw + 0.5D0 ))
       rden = cden*CONJG(cden)
       rden = 1D0 / rden
       ssx = -Omega2 * CONJG(cden) * rden * delw
     else
       branch = 3
       sch = 0.0d0
       ssx = 0.0d0
     endif

     ssxcutoff = sig_sexcut*abs(I_eps)
     if (abs(ssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0) ssx=0.0d0
     ! ---- end verbatim block ------------------------------------------------

     ! Accumulation of lines 1854-1855 and 1908-1915, with the external factor
     ! aqsntemp*CONJG(aqsmtemp)*vcoul(igp) divided out and occ = 1.
     occupied = -1.0d0*ssx + 0.5d0*sch
     ! The unoccupied predicate is independent of the occupied branch.
     empty = 0.0d0
     if (wdiffr.gt.limittwo .and. delwr.lt.limitone) then
       empty = 0.5d0 * real(delw * I_eps, DP)
     endif

     write(*,'(es23.16,1x,es23.16,1x,i1,1x,es23.16,1x,es23.16,1x,es23.16,1x,es23.16,1x,es23.16)') &
          offset, wxt, branch, sch, ssx, occupied, empty, occupied*RYD
  end do

end program kernel_transcript
