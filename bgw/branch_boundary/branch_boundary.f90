! Source-level GPP branch-boundary and occupation sweep (T-005).
!
! This is NOT BerkeleyGW. It is a standalone single-file real-flavor driver that
! re-executes the arithmetic statements of the inner `ig` loop of
! `sigma_gpp_cpu` so that branch selection, binary64 evaluation order, the
! `sexcut` clamp and the occupation factor can be observed at chosen inputs.
! Everything around those statements --- the G/G' loops, matrix elements
! `aqsntemp`/`aqsmtemp`, the Coulomb factor `vcoul`, MPI/OpenMP --- is removed,
! so the reported values are per-(ig,igp) local values with the common factor
! `aqsntemp*MYCONJG(aqsmtemp)*vcoul(igp)` divided out. Running this program says
! nothing about any production BerkeleyGW calculation or any material.
!
! Provenance of every statement marked `!>BGW`:
!
!   tarball       sha256 1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49
!   mtxel_cor.f90 sha256 8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd
!                 (BerkeleyGW-4.0, Sigma/mtxel_cor.f90, 3968 lines)
!
!   Sigma/mtxel_cor.f90:772-795     GPP setup: the abs(wtilde2) < TOL_Small
!                                   cycle and the sig%invalid_gpp_mode policy
!                                   that decides wtilde for wtilde2 < 0
!   Sigma/mtxel_cor.f90:1698-1699   limitone, limittwo
!   Sigma/mtxel_cor.f90:1746        wx clamp at TOL_Zero
!   Sigma/mtxel_cor.f90:1810-1848   occupied inner loop: delw/delwr/wdiffr,
!                                   the two-conjunct predicate, both branches,
!                                   the ssxcutoff clamp
!   Sigma/mtxel_cor.f90:1854-1855   ssx_array/sch_array accumulation weights
!   Sigma/mtxel_cor.f90:1906-1916   -occ*SX and +CH accumulation
!   Sigma/inread.f90:151-152        sig%gamma = 0.5, sig%sexcut = 4.0 defaults
!   Common/nrtype.f90:155,161-162   RYD, TOL_Small, TOL_Zero
!
! Declared kinds are taken from the subroutine headers and are reproduced, not
! repaired (`Sigma/mtxel_cor.f90:138,142,1665-1668`):
!
!   SCALAR (= real(DP) in the real flavor) :: Omega2, wtilde2, ssx, sch
!   complex(DPC)                           :: wtilde, delw, wdiff, cden
!   real(DP)                               :: delwr, wdiffr, rden, wxt, ssxcutoff
!
! so `wtilde2 = wtilde**2`, `sch = delw*I_eps`, `rden = cden*CONJG(cden)` and
! `ssx = Omega2*CONJG(cden)*rden` are complex-to-real intrinsic assignments that
! keep the real part. The real-flavor macro `MYCONJG(x)` expands to `(x)`, NOT
! to `conjg(x)` (`Common/f_defs.h:48`), so the near-pole branch squares `cden`
! instead of taking its modulus. Both spellings agree here only because the
! restriction to positive real modes makes `cden` real; the source spelling is
! reproduced anyway.
!
! Output is a tagged, whitespace-separated table on stdout. Each data line
! begins with a tag; `#` lines are metadata. All reals are printed with 17
! significant digits, which round-trips binary64.

program branch_boundary
  use, intrinsic :: iso_fortran_env, only: int64
  implicit none

  integer, parameter :: DP  = kind(1.0d0)
  integer, parameter :: DPC = kind((1.0d0,1.0d0))

  !> Everything one evaluation of the transcribed statements produces.
  !> `*_pre` is the value the source holds after line 1843, before the
  !> `ssxcutoff` clamp of line 1848; the unsuffixed field is the value after
  !> it. `cut_*` records that the clamp condition itself fired, so that a
  !> clamped zero is never confused with an algebraic zero. `g*`/`n*` are the
  !> generic and near-pole candidates forced at the same inputs: they are
  !> counterfactual diagnostics, kept separate from the selected result.
  type :: kern_t
    real(DP)     :: wxt, wdiffr, delwr, ssxcutoff
    complex(DPC) :: wtilde, delw
    logical      :: c1, c2
    integer      :: branch
    real(DP)     :: ssx_pre,  ssx,  sch
    real(DP)     :: gssx_pre, gssx, gsch
    real(DP)     :: nssx_pre, nssx, nsch
    logical      :: cut_sel, cut_gen, cut_np
  end type kern_t

  !>BGW Common/nrtype.f90:161-162,155
  real(DP), parameter :: TOL_Small = 1.0d-6
  real(DP), parameter :: TOL_Zero  = 1.0d-12
  real(DP), parameter :: RYD       = 13.60569253d0
  !>BGW Sigma/inread.f90:151-152 (defaults of `gpp_broadening`, `gpp_sexcutoff`)
  real(DP), parameter :: sig_gamma  = 0.5d0
  real(DP), parameter :: sig_sexcut = 4.0d0

  real(DP) :: limitone, limittwo

  character(len=*), parameter :: RFMT = 'es24.16'

  !>BGW Sigma/mtxel_cor.f90:1698-1699
  limitone=1D0/(TOL_Small*4D0)
  limittwo=sig_gamma**2

  call emit_metadata()
  call boundary_cases()
  call occupation_cases()
  call invariance_cases()

contains

  ! ---------------------------------------------------------------------------
  ! Sigma/mtxel_cor.f90:772-794, the GPP setup that decides `wtilde` from
  ! `wtilde2 = Omega2/I_epsggp`, reproduced because it is what determines which
  ! modes can reach the inner loop at all.
  !
  ! Note the filter at line 774 is on `abs(wtilde2)`: a sufficiently NEGATIVE
  ! wtilde2 passes it, and `sig%invalid_gpp_mode` then decides the mode. Policy
  ! 0 is one explicit non-cycled route to wtilde = (0,0). Earlier setup cycles
  ! can also leave the zero-initialized wtilde_array entry unchanged.
  ! ---------------------------------------------------------------------------
  subroutine setup_wtilde(wtilde2_in, invalid_gpp_mode, wtilde, cycled)
    real(DP),     intent(in)  :: wtilde2_in
    integer,      intent(in)  :: invalid_gpp_mode
    complex(DPC), intent(out) :: wtilde
    logical,      intent(out) :: cycled

    real(DP) :: wtilde2

    wtilde2 = wtilde2_in
    wtilde  = CMPLX(0d0, 0d0, kind=DPC)

    !>BGW 774  (note: abs(), so wtilde2 << 0 survives this filter)
    if (abs(wtilde2) .lt. TOL_Small) then
      cycled = .true.
      return
    end if
    cycled = .false.

    !>BGW 778-794
    if (wtilde2 < 0) then
      select case (invalid_gpp_mode)
        case (0) ! Skip invalid GPP mode and ignore its contribution.
          wtilde = (0d0,0d0)
        case (1) ! "Find" a purely imaginary mode frequency.
          wtilde = sqrt(CMPLX(wtilde2, 0d0, kind=DPC))
        case (2) ! Fixed mode frequency of 2 Ry.
          wtilde = CMPLX(2d0*RYD, 0d0, kind=DPC)
        case (3) ! Static COHSEX for that mode.
          wtilde = CMPLX(1d0/TOL_Zero, 0d0, kind=DPC)
        case default
          wtilde = CMPLX(1d0/TOL_Zero, 0d0, kind=DPC)
      endselect
    else
      wtilde = CMPLX(sqrt(wtilde2), 0d0, kind=DPC)
    endif
  end subroutine setup_wtilde

  ! ---------------------------------------------------------------------------
  ! One evaluation of the kernel statements at one (I_eps, wtilde, wxt).
  !
  ! `k%ssx`/`k%sch` are the values the source would actually hold after line
  ! 1848. `k%*_pre` are the pre-clamp values; the clamp is never inferred from
  ! the post-clamp fields.
  ! ---------------------------------------------------------------------------
  subroutine eval_point(I_eps, wt, wxt_raw, k)
    real(DP), intent(in)  :: I_eps, wt, wxt_raw
    type(kern_t), intent(out) :: k
    ! Positive real mode, as produced by Sigma/mtxel_cor.f90:793.
    call eval_mode(I_eps, CMPLX(wt, 0d0, kind=DPC), wxt_raw, k)
  end subroutine eval_point

  subroutine eval_mode(I_eps, wtilde_in, wxt_raw, k)
    real(DP),     intent(in)  :: I_eps, wxt_raw
    complex(DPC), intent(in)  :: wtilde_in
    type(kern_t), intent(out) :: k

    real(DP) :: rden, ssxcutoff, Omega2, wtilde2, wxt, wdiffr, delwr
    real(DP) :: ssx_pre, ssx, sch, gssx_pre, gssx, gsch, nssx_pre, nssx, nsch
    logical :: c1, c2
    integer :: branch
    complex(DPC) :: wtilde, delw, wdiff, cden

    wxt = wxt_raw
    !>BGW Sigma/mtxel_cor.f90:1746
    if (abs(wxt) .lt. TOL_Zero) wxt = TOL_Zero

    !>BGW 1810  (wtilde comes from wtilde_array, i.e. from setup_wtilde)
    wtilde = wtilde_in

    ! ---- Sigma/mtxel_cor.f90:1811-1824, verbatim ----------------------------
    !>BGW 1811
    wtilde2 = wtilde**2
    !>BGW 1812
    Omega2 = wtilde2 * I_eps

    !>BGW 1817
    wdiff = wxt - wtilde

    !>BGW 1819-1824
    cden = wdiff
    rden = cden * CONJG(cden)
    rden = 1D0 / rden
    delw = wtilde * CONJG(cden) * rden
    delwr = delw*CONJG(delw)
    wdiffr = wdiff*CONJG(wdiff)
    ! ---- end verbatim -------------------------------------------------------

    ! The two conjuncts of the predicate at line 1828, reported separately.
    c1 = (wdiffr.gt.limittwo)
    c2 = (delwr.lt.limitone)

    ! ---- Sigma/mtxel_cor.f90:1828-1843, verbatim ----------------------------
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
      rden = cden*(cden)
      rden = 1D0 / rden
      ssx = -Omega2 * (cden) * rden * delw
    else
      branch = 3
      sch = 0.0d0
      ssx = 0.0d0
    endif
    ssx_pre = ssx

    !>BGW 1847-1848
    ssxcutoff = sig_sexcut*abs(I_eps)
    k%cut_sel = (abs(ssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0)
    if (abs(ssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0) ssx=0.0d0
    ! ---- end verbatim -------------------------------------------------------

    ! ---- counterfactual generic candidate: lines 1829-1833 forced -----------
    gsch = delw * I_eps
    cden = wxt**2 - wtilde2
    rden = cden*CONJG(cden)
    rden = 1D0 / rden
    gssx = Omega2 * CONJG(cden) * rden
    gssx_pre = gssx
    k%cut_gen = (abs(gssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0)
    if (abs(gssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0) gssx=0.0d0

    ! ---- counterfactual near-pole candidate: lines 1835-1839 forced ---------
    nsch = 0.0d0
    cden = (4.0d0 * wtilde2 * (delw + 0.5D0 ))
    rden = cden*(cden)
    rden = 1D0 / rden
    nssx = -Omega2 * (cden) * rden * delw
    nssx_pre = nssx
    k%cut_np = (abs(nssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0)
    if (abs(nssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0) nssx=0.0d0

    k%wxt = wxt
    k%wdiffr = wdiffr
    k%delwr = delwr
    k%ssxcutoff = ssxcutoff
    k%wtilde = wtilde
    k%delw = delw
    k%c1 = c1
    k%c2 = c2
    k%branch = branch
    k%ssx_pre = ssx_pre;  k%ssx  = ssx;  k%sch  = sch
    k%gssx_pre = gssx_pre; k%gssx = gssx; k%gsch = gsch
    k%nssx_pre = nssx_pre; k%nssx = nssx; k%nsch = nsch
  end subroutine eval_mode

  !> Local accumulated value with the common factor divided out:
  !> `asxtemp -= ssx*occ*vcoul` (line 1908) and `achtemp += 0.5*sch*vcoul`
  !> (lines 1855, 1915).
  pure function local_value(occ, ssx, sch) result(v)
    real(DP), intent(in) :: occ, ssx, sch
    real(DP) :: v
    v = -occ*ssx + 0.5d0*sch
  end function local_value

  !> The complete predicate of line 1828 as a function of `wxt` alone.
  function predicate(I_eps, wt, wxt_raw) result(p)
    real(DP), intent(in) :: I_eps, wt, wxt_raw
    logical :: p
    type(kern_t) :: k
    call eval_point(I_eps, wt, wxt_raw, k)
    p = k%c1 .and. k%c2
  end function predicate

  !> Bisect on the binary64 bit patterns of `|wxt|` until `w_false` and
  !> `w_true` are adjacent representable numbers straddling the predicate
  !> surface. Both brackets must be finite and of the same sign; for a fixed
  !> sign, IEEE bit order of the magnitude is numeric order of the magnitude.
  !> This is the exact machine boundary, not a decimal approximation.
  subroutine bisect_boundary(I_eps, wt, w_true_in, w_false_in, w_true, w_false, steps)
    real(DP), intent(in)  :: I_eps, wt, w_true_in, w_false_in
    real(DP), intent(out) :: w_true, w_false
    integer,  intent(out) :: steps
    integer(int64) :: bt, bf, bm
    real(DP) :: wm, wsign

    if (w_true_in*w_false_in <= 0.0d0) stop 'bracket: must be finite and same sign'
    wsign = sign(1.0d0, w_true_in)
    if (.not. predicate(I_eps, wt, w_true_in)) stop 'bracket: w_true_in is false'
    if (predicate(I_eps, wt, w_false_in))      stop 'bracket: w_false_in is true'
    bt = transfer(abs(w_true_in), bt)
    bf = transfer(abs(w_false_in), bf)
    steps = 0
    do while (abs(bt - bf) > 1_int64)
      bm = bf + (bt - bf)/2_int64
      wm = wsign * transfer(bm, wm)
      if (predicate(I_eps, wt, wm)) then
        bt = bm
      else
        bf = bm
      end if
      steps = steps + 1
      if (steps > 200) stop 'bisection did not converge'
    end do
    w_true  = wsign * transfer(bt, w_true)
    w_false = wsign * transfer(bf, w_false)
  end subroutine bisect_boundary

  subroutine emit_metadata()
    write(*,'(a)') '# T-005 source-level GPP branch-boundary and occupation sweep'
    write(*,'(a)') '# not a BerkeleyGW run; local values, common factors divided out'
    write(*,'(a)') '# mtxel_cor_sha256 8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd'
    write(*,'(a,'//RFMT//')') '# TOL_Small  ', TOL_Small
    write(*,'(a,'//RFMT//')') '# TOL_Zero   ', TOL_Zero
    write(*,'(a,'//RFMT//')') '# sig_gamma  ', sig_gamma
    write(*,'(a,'//RFMT//')') '# sig_sexcut ', sig_sexcut
    write(*,'(a,'//RFMT//')') '# limitone   ', limitone
    write(*,'(a,'//RFMT//')') '# limittwo   ', limittwo
    write(*,'(a,'//RFMT//')') '# RYD        ', RYD
    write(*,'(a,i0)')         '# epsilon_bits ', digits(1.0d0)
    write(*,'(a)') '# COLUMNS BOUNDARY case ieps wt w_false w_true bits_false bits_true steps'
    write(*,'(a)') '# COLUMNS SWEEP case label ieps wt occ wxt bits d wdiffr delwr c1 c2 branch' // &
                   ' ssx_pre ssx sch value gen_value np_value gen_ssx np_ssx gen_sch np_sch' // &
                   ' gen_ssx_pre np_ssx_pre value_pre gen_value_pre np_value_pre' // &
                   ' ssxcutoff cut_sel cut_gen cut_np'
    write(*,'(a)') '# COLUMNS OCC point ieps wt wxt occ gen_value np_value delta closed_form'
    write(*,'(a)') '# COLUMNS OCCCHK point ratio_ref max_rel_spread delta_at_occ_one'
    write(*,'(a)') '# COLUMNS INVSHIFT point shift wxt_base wxt_shift value_base value_shift'
    write(*,'(a)') '# COLUMNS INVSCALE point lambda gen_value np_value delta' // &
                   ' rel_gen rel_np rel_delta'
    write(*,'(a)') '# COLUMNS BRANCH3 label policy wtilde2_in cycled wtilde_re wtilde_im' // &
                   ' ieps wxt wdiffr delwr c1 c2 branch ssx sch value'
  end subroutine emit_metadata

  subroutine emit_sweep_row(case_name, label, I_eps, wt, occ, wxt_raw)
    character(len=*), intent(in) :: case_name, label
    real(DP), intent(in) :: I_eps, wt, occ, wxt_raw
    type(kern_t) :: k
    integer(int64) :: bits

    call eval_point(I_eps, wt, wxt_raw, k)
    bits = transfer(k%wxt, bits)
    write(*,'(a,1x,a,1x,a,4('//RFMT//',1x),i0,1x,3('//RFMT//',1x),i1,1x,i1,1x,i1,' // &
             '1x,16('//RFMT//',1x),i1,1x,i1,1x,i1)') &
      'SWEEP', trim(case_name), trim(label), I_eps, wt, occ, k%wxt, bits, &
      k%wxt - wt, k%wdiffr, k%delwr, merge(1,0,k%c1), merge(1,0,k%c2), k%branch, &
      k%ssx_pre, k%ssx, k%sch, local_value(occ, k%ssx, k%sch), &
      local_value(occ, k%gssx, k%gsch), local_value(occ, k%nssx, k%nsch), &
      k%gssx, k%nssx, k%gsch, k%nsch, &
      k%gssx_pre, k%nssx_pre, local_value(occ, k%ssx_pre, k%sch), &
      local_value(occ, k%gssx_pre, k%gsch), local_value(occ, k%nssx_pre, k%nsch), &
      k%ssxcutoff, merge(1,0,k%cut_sel), merge(1,0,k%cut_gen), merge(1,0,k%cut_np)
  end subroutine emit_sweep_row

  subroutine boundary_cases()
    ! Unclamped cases: wxt > 0 everywhere, so line 1848 can never fire.
    call one_boundary('A+',  1.0d0,   1.0d0,   1.6d0,   1.4d0)
    call one_boundary('A-',  1.0d0,   1.0d0,   0.4d0,   0.6d0)
    call one_boundary('B+',  1.0d0, 300.0d0, 301.0d0, 300.4d0)
    ! Clamp-active case: a source-valid positive real mode
    ! (wtilde2 = 0.0676 >= TOL_Small, so line 774 does not cycle it) with
    ! wxt < 0 adjacent to the negative |d| = gamma surface. Both |ssx|
    ! candidates exceed ssxcutoff = 4*|I_eps| there, so line 1848 fires.
    call one_boundary('C-',  1.0d0,  0.26d0,  -0.30d0, -0.20d0)
    call branch3_cases()
  end subroutine boundary_cases

  !> One predicate surface: locate it exactly, then sweep the representable
  !> neighbours and several wider offsets on both sides, at occ = 1 and 0.5.
  subroutine one_boundary(case_name, I_eps, wt, w_true_in, w_false_in)
    character(len=*), intent(in) :: case_name
    real(DP), intent(in) :: I_eps, wt, w_true_in, w_false_in
    real(DP), parameter :: offs(6) = [1.0d-12, 1.0d-9, 1.0d-6, 1.0d-3, 1.0d-2, 1.0d-1]
    real(DP), parameter :: occs(2) = [1.0d0, 0.5d0]
    real(DP) :: w_true, w_false, sgn, w
    integer(int64) :: bt, bf
    integer :: steps, j, k
    character(len=16) :: label

    call bisect_boundary(I_eps, wt, w_true_in, w_false_in, w_true, w_false, steps)
    bt = transfer(w_true, bt)
    bf = transfer(w_false, bf)
    write(*,'(a,1x,a,4('//RFMT//',1x),i0,1x,i0,1x,i0)') &
      'BOUNDARY', trim(case_name), I_eps, wt, w_false, w_true, bf, bt, steps

    ! Direction in which the predicate becomes true.
    sgn = sign(1.0d0, w_true - w_false)

    do k = 1, size(occs)
      ! Representable neighbours: two on the false side, two on the true side.
      call emit_sweep_row(case_name, 'ulpF-2', I_eps, wt, occs(k), &
                          nearest(nearest(w_false, -sgn), -sgn))
      call emit_sweep_row(case_name, 'ulpF-1', I_eps, wt, occs(k), nearest(w_false, -sgn))
      call emit_sweep_row(case_name, 'ulpF-0', I_eps, wt, occs(k), w_false)
      call emit_sweep_row(case_name, 'ulpT+0', I_eps, wt, occs(k), w_true)
      call emit_sweep_row(case_name, 'ulpT+1', I_eps, wt, occs(k), nearest(w_true, sgn))
      call emit_sweep_row(case_name, 'ulpT+2', I_eps, wt, occs(k), &
                          nearest(nearest(w_true, sgn), sgn))
      ! Wider offsets, on the true side and on the false side.
      do j = size(offs), 1, -1
        write(label,'(a,es8.1)') 'far-', offs(j)
        call squeeze(label)
        w = w_false - sgn*offs(j)
        call emit_sweep_row(case_name, label, I_eps, wt, occs(k), w)
      end do
      do j = 1, size(offs)
        write(label,'(a,es8.1)') 'far+', offs(j)
        call squeeze(label)
        w = w_true + sgn*offs(j)
        call emit_sweep_row(case_name, label, I_eps, wt, occs(k), w)
      end do
    end do
  end subroutine one_boundary

  subroutine squeeze(s)
    character(len=*), intent(inout) :: s
    character(len=len(s)) :: t
    integer :: i, n
    t = ''
    n = 0
    do i = 1, len_trim(s)
      if (s(i:i) /= ' ') then
        n = n + 1
        t(n:n) = s(i:i)
      end if
    end do
    s = t
  end subroutine squeeze

  !> Branch 3 requires `delwr <= TOL_Zero` while `wdiffr <= limittwo`, i.e.
  !> `|wdiff| <= gamma = 0.5` and `|wtilde| <= sqrt(TOL_Zero)*|wdiff| <= 5e-7`
  !> simultaneously. A mode that survives line 774 has `|wtilde2| >= TOL_Small`;
  !> if it is also positive-real then `|wtilde| = sqrt(wtilde2) >= 1e-3`, which
  !> contradicts the above by three orders of magnitude. So an ordinary
  !> surviving positive-real mode cannot reach branch 3.
  !>
  !> The zero mode is nonetheless reachable in source: line 774 filters on
  !> `abs(wtilde2)`, so a sufficiently negative `wtilde2` passes, and
  !> `sig%invalid_gpp_mode = 0` then assigns `wtilde = (0,0)` at line 782. These
  !> rows walk every `invalid_gpp_mode` policy at the same negative `wtilde2`,
  !> plus the cycled case and the smallest surviving positive-real mode.
  subroutine branch3_cases()
    call emit_branch3('policy0',  -1.0d0,  0, 1.0d0, 0.1d0)
    call emit_branch3('policy0f', -1.0d0,  0, 1.0d0, 1.0d0)
    call emit_branch3('policy1',  -1.0d0,  1, 1.0d0, 0.1d0)
    call emit_branch3('policy2',  -1.0d0,  2, 1.0d0, 0.1d0)
    call emit_branch3('policy3',  -1.0d0,  3, 1.0d0, 0.1d0)
    call emit_branch3('policy9',  -1.0d0,  9, 1.0d0, 0.1d0)
    ! Below TOL_Small in absolute value: cycled at line 774, never evaluated.
    call emit_branch3('cycled',    1.0d-9, 0, 1.0d0, 0.1d0)
    call emit_branch3('cycledneg',-1.0d-9, 0, 1.0d0, 0.1d0)
    ! The smallest surviving positive-real mode, at the wxt that maximises
    ! |wdiff| while keeping the first conjunct false: still branch 2.
    call emit_branch3('minmode',   TOL_Small, 0, 1.0d0, sqrt(TOL_Small) - 0.5d0)
  end subroutine branch3_cases

  subroutine emit_branch3(label, wtilde2_in, invalid_gpp_mode, I_eps, wxt_raw)
    character(len=*), intent(in) :: label
    real(DP), intent(in) :: wtilde2_in, I_eps, wxt_raw
    integer,  intent(in) :: invalid_gpp_mode
    complex(DPC) :: wtilde
    logical :: cycled
    type(kern_t) :: k
    integer :: branch

    call setup_wtilde(wtilde2_in, invalid_gpp_mode, wtilde, cycled)
    call eval_mode(I_eps, wtilde, wxt_raw, k)
    ! branch = -1 means the mode never reaches the inner loop at all.
    branch = k%branch
    if (cycled) branch = -1
    write(*,'(a,1x,a,1x,i0,1x,'//RFMT//',1x,i1,1x,6('//RFMT//',1x),' // &
             'i1,1x,i1,1x,i2,1x,3('//RFMT//',1x))') &
      'BRANCH3', trim(label), invalid_gpp_mode, wtilde2_in, merge(1,0,cycled), &
      dble(wtilde), aimag(wtilde), I_eps, k%wxt, k%wdiffr, k%delwr, &
      merge(1,0,k%c1), merge(1,0,k%c2), branch, &
      k%ssx, k%sch, local_value(1.0d0, k%ssx, k%sch)
  end subroutine emit_branch3

  ! ---------------------------------------------------------------------------
  ! Occupation linearity at fixed nonsingular points, away from the sexcut
  ! clamp (which additionally needs wxt < 0) and away from overflow.
  ! ---------------------------------------------------------------------------
  subroutine occupation_cases()
    integer, parameter :: NP = 4
    real(DP), parameter :: ieps(NP) = [ 1.00d0,  0.37d0, -0.80d0, 2.00d0]
    real(DP), parameter :: wts(NP)  = [ 1.00d0,  2.50d0,  1.70d0, 0.75d0]
    real(DP), parameter :: wxs(NP)  = [ 2.00d0,  4.00d0,  0.30d0, 3.00d0]
    real(DP), parameter :: occs(4)  = [1.0d0, 0.75d0, 0.5d0, 0.25d0]
    character(len=2), parameter :: names(NP) = ['P1','P2','P3','P4']
    type(kern_t) :: kv
    real(DP) :: wxt
    real(DP) :: gv, nv, delta, closed, Omega2, ratio(4), ref, spread, d_one
    integer :: p, k

    do p = 1, NP
      d_one = 0.0d0
      do k = 1, size(occs)
        call eval_point(ieps(p), wts(p), wxs(p), kv)
        wxt = kv%wxt
        gv = local_value(occs(k), kv%gssx, kv%gsch)
        nv = local_value(occs(k), kv%nssx, kv%nsch)
        ! Sign convention: generic candidate MINUS near-pole candidate.
        delta = gv - nv
        ! Closed form of GW.GPP.BGW4.branch_mismatch, evaluated in binary64.
        Omega2 = wts(p)**2 * ieps(p)
        closed = (1.0d0 - occs(k)) * ( Omega2/(2.0d0*wts(p)*(wxt + wts(p))) &
                                     + Omega2/((wxt - wts(p))*(wxt + wts(p))) )
        write(*,'(a,1x,a,8('//RFMT//',1x))') 'OCC', names(p), ieps(p), wts(p), wxt, &
          occs(k), gv, nv, delta, closed
        if (occs(k) == 1.0d0) then
          d_one = delta
          ratio(k) = 0.0d0
        else
          ratio(k) = delta / (1.0d0 - occs(k))
        end if
      end do
      ref = ratio(2)
      spread = 0.0d0
      do k = 2, size(occs)
        spread = max(spread, abs(ratio(k) - ref)/abs(ref))
      end do
      write(*,'(a,1x,a,3('//RFMT//',1x))') 'OCCCHK', names(p), ref, spread, d_one
    end do
  end subroutine occupation_cases

  ! ---------------------------------------------------------------------------
  ! Secondary invariance checks from the external review.
  ! ---------------------------------------------------------------------------
  subroutine invariance_cases()
    ! The last two shifts are deliberately past the point where `E + C` and
    ! `eps + C` still round exactly: the invariance is exact in real arithmetic
    ! but only as exact as the binary64 subtraction that forms `wxt`.
    real(DP), parameter :: shifts(9) = [0.0d0, 1.0d0, 1.0d3, 1.0d6, 1.0d9, &
                                        1.0d12, 1.0d15, 1.0d16, 1.0d17]
    real(DP), parameter :: lams(5)   = [1.0d0, 2.0d0, 0.25d0, -1.0d0, -3.5d0]
    real(DP), parameter :: E0 = 3.25d0, eps0 = 1.25d0, wt = 1.0d0, ieps0 = 0.8d0
    type(kern_t) :: k
    real(DP) :: wxt_base, v_base, wxt_s, v_s, gv, nv, delta
    real(DP) :: gv1, nv1, d1, occ
    integer :: j

    occ = 0.5d0

    ! (a) Common energy-zero shift. The kernel sees only wxt; the source builds
    ! it as `e_lk + sig%dw*(iw-2) - e_n1kq` (line 1744), so the shift is applied
    ! to both energies BEFORE the binary64 subtraction, exactly as a rerun with
    ! a different energy zero would.
    wxt_base = (E0 + shifts(1)) - (eps0 + shifts(1))
    call eval_point(ieps0, wt, wxt_base, k)
    v_base = local_value(occ, k%ssx, k%sch)
    do j = 1, size(shifts)
      wxt_s = (E0 + shifts(j)) - (eps0 + shifts(j))
      call eval_point(ieps0, wt, wxt_s, k)
      v_s = local_value(occ, k%ssx, k%sch)
      write(*,'(a,1x,a,5('//RFMT//',1x))') 'INVSHIFT', 'S1', shifts(j), &
        wxt_base, wxt_s, v_base, v_s
    end do

    ! (b) Scaling and sign flip of I_eps. Omega2 is linear in I_eps and sch is
    ! linear in I_eps, so both candidates and their discrepancy must scale by
    ! lambda. The sexcut clamp also scales with |I_eps|, so it cannot break this
    ! at these inputs (wxt > 0 disables it outright).
    call eval_point(ieps0, wt, E0 - eps0, k)
    gv1 = local_value(occ, k%gssx, k%gsch)
    nv1 = local_value(occ, k%nssx, k%nsch)
    d1  = gv1 - nv1
    do j = 1, size(lams)
      call eval_point(lams(j)*ieps0, wt, E0 - eps0, k)
      gv = local_value(occ, k%gssx, k%gsch)
      nv = local_value(occ, k%nssx, k%nsch)
      delta = gv - nv
      write(*,'(a,1x,a,7('//RFMT//',1x))') 'INVSCALE', 'S1', lams(j), gv, nv, delta, &
        abs(gv - lams(j)*gv1)/abs(lams(j)*gv1), &
        abs(nv - lams(j)*nv1)/abs(lams(j)*nv1), &
        abs(delta - lams(j)*d1)/abs(lams(j)*d1)
    end do
  end subroutine invariance_cases

end program branch_boundary
