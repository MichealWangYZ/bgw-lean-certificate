#!/usr/bin/env python3
"""Apply the BGW-M4-R1 export instrumentation to a copy of the pinned tree.

Write statements only.  Every production assignment is left byte-for-byte in
place; each insertion is anchored on an exact, unique source line and the
script fails if an anchor is missing or ambiguous.  Records go to
`m4r1_dump.dat` in the run directory, one line each, with every
floating-point value as its raw IEEE-754 bit pattern (signed int64) so the
consumer never parses a decimal rendering.

    python3 instrument_r1.py TREE          # patch TREE in place
"""
import pathlib
import sys

OPEN = "open(unit=791, file='m4r1_dump.dat', position='append', status='unknown')"
B = "transfer(dble({}), m4_b)"

SIGMA_MAIN_DECL_ANCHOR = "  integer, allocatable :: ind(:), indinv(:)\n"
SIGMA_MAIN_DECL = """#ifndef CPLX
  integer :: m4_ig, m4_i
  integer(8) :: m4_b
#endif
"""

GMAP_ANCHOR = "      call timing%stop(timing%gmap)\n"
GMAP_EXPORT = f"""#ifndef CPLX
      ! BGW-M4-R1: the rq -> stored-block map actually used for this irq.
      {OPEN}
      write(791,'(A,9(1X,I0),6(1X,I0))') 'RQ', irq, nm, itran, kg(1), kg(2), kg(3), &
        ncouls, nmtx, nrq, ({B.format('rq(m4_i,irq)')}, m4_i=1,3), &
        ({B.format('qk(m4_i)')}, m4_i=1,3)
      write(791,'(A,1X,I0,9(1X,I0),3(1X,I0))') 'SYM', irq, &
        ((syms%mtrx(m4_i,m4_ig,itran), m4_ig=1,3), m4_i=1,3), &
        ({B.format('syms%tnp(m4_i,itran)')}, m4_i=1,3)
      do m4_ig = 1, ncouls
        if (ind(m4_ig) .gt. 0) then
          write(791,'(A,3(1X,I0),6(1X,I0),1X,I0)') 'MAP', irq, m4_ig, ind(m4_ig), &
            gvec%components(:,isrtrq(m4_ig)), gvec%components(:,isrtq(ind(m4_ig))), &
            {B.format('ph(m4_ig)')}
        else
          write(791,'(A,3(1X,I0),3(1X,I0))') 'MAPNONE', irq, m4_ig, ind(m4_ig), &
            gvec%components(:,isrtrq(m4_ig))
        endif
      enddo
      close(791)
#endif
"""

WING_ANCHOR = "        enddo ! igp\n"
WING_EXPORT = f"""#ifndef CPLX
        ! BGW-M4-R1: operands of the wing normalization just applied to `eps`.
        {OPEN}
        write(791,'(A,1X,I0,5(1X,I0),1X,I0,1X,I0,7(1X,I0))') 'WING', irq, nm, iout, &
          sig%icutv, sig%iscreen, merge(1, 0, sig%averagew), &
          merge(1, 0, nm .eq. 1), merge(1, 0, qlen**2 .lt. sig%avgcut), &
          {B.format('vcoul(1)')}, {B.format('qlen')}, {B.format('q0len')}, &
          {B.format('oneoverq')}, {B.format('fact')}, {B.format('sig%avgcut')}, &
          {B.format('PI_D')}
        close(791)
#endif
"""

MTXEL_DECL_ANCHOR ="  real(DP) :: e_lk, e_n1kq, lambda, phi, freq0, wx, occ\n"
MTXEL_DECL = """#ifndef CPLX
  integer :: m4_i
  integer(8) :: m4_b
  integer(8), save :: m4_occ = 0
#endif
"""

MTXEL_ENTRY_ANCHOR = "    select case(sig%freq_dep)\n    case(0,1)\n      epstemp(:)=eps(:,my_igp)\n"
MTXEL_ENTRY = f"""#ifndef CPLX
    ! BGW-M4-R1: which stored eps column this G' reads.
    {OPEN}
    write(791,'(A,6(1X,I0),1X,I0,3(1X,I0))') 'COL', in, il, ispin, my_igp, indigp, igp, &
      {B.format('coulfact')}, ({B.format('qk(m4_i)')}, m4_i=1,3)
    close(791)
#endif
"""

SURVIVE_ANCHOR = """          endselect
        else
          wtilde = CMPLX(sqrt(dble(wtilde2)), 0d0)
        endif
        wtilde_array(ig,my_igp) = wtilde
"""
SURVIVE_EXPORT = f"""#ifndef CPLX
        ! BGW-M4-R1: reached only by modes that passed every `cycle` above.
        m4_occ = m4_occ + 1
        {OPEN}
        write(791,'(A,1X,I0,6(1X,I0),8(1X,I0))') 'GPP', m4_occ, ig, igp, my_igp, indigp, &
          ind(ig), merge(1, 0, dble(wtilde2) > 0d0), &
          {B.format('ph(ig)')}, {B.format('ph(igp)')}, {B.format('epstemp(ind(ig))')}, &
          {B.format('epsggp')}, {B.format('I_epsggp')}, {B.format('Omega2')}, &
          {B.format('wtilde2')}, {B.format('dble(wtilde)')}
        close(791)
#endif
"""

WPEFF_DECL_ANCHOR = "  integer :: ig, igadd, igpadd, kadd, gg(3)\n"
WPEFF_DECL = """#ifndef CPLX
  integer :: m4_i, m4_j
  integer(8) :: m4_b
#endif
"""
WPEFF_ANCHOR = "  enddo !! g loop\n"
WPEFF_EXPORT = f"""#ifndef CPLX
  ! BGW-M4-R1: every primitive operand of wpmtx for this G', then its value.
  {OPEN}
  write(791,'(A,1X,I0,2(1X,I0),9(1X,I0),1X,I0)') 'WPG', igp, ncouls, nspin, &
    (({B.format('crys%bdot(m4_i,m4_j)')}, m4_j=1,3), m4_i=1,3), {B.format('coulfact')}
  write(791,'(A,5(1X,I0),3(1X,I0))') 'WPF', igp, {B.format('wpg%wpsq(1)')}, &
    {B.format('wpg%nelec(1)')}, {B.format('fact')}, merge(1, 0, q_is_not_zero), &
    ({B.format('qk(m4_i)')}, m4_i=1,3)
  do ig = 1, ncouls
    igadd = isrtrq(ig)
    igpadd = isrtrq(igp)
    gg(:) = gvec%components(:, igadd) - gvec%components(:, igpadd)
    call findvector(kadd, gg, gvec)
    if (kadd .eq. 0) then
      write(791,'(A,3(1X,I0))') 'WPNONE', igp, ig, {B.format('wpmtx(ig)')}
    else
      write(791,'(A,2(1X,I0),6(1X,I0),3(1X,I0))') 'WP', igp, ig, &
        gvec%components(:, igadd), gvec%components(:, igpadd), &
        {B.format('vcoul(ig)')}, {B.format('sum(wpg%rho(kadd,1:nspin))')}, &
        {B.format('wpmtx(ig)')}
    endif
  enddo
  close(791)
#endif
"""


def insert(path, anchor, text, *, before=False):
    src = path.read_text()
    n = src.count(anchor)
    if n != 1:
        sys.exit(f"{path}: anchor found {n} times, expected 1:\n{anchor}")
    new = text + anchor if before else anchor + text
    path.write_text(src.replace(anchor, new))


def main(tree):
    t = pathlib.Path(tree)
    sm = t / "Sigma/sigma_main.f90"
    insert(sm, SIGMA_MAIN_DECL_ANCHOR, SIGMA_MAIN_DECL)
    insert(sm, WING_ANCHOR, WING_EXPORT)
    insert(sm, GMAP_ANCHOR, GMAP_EXPORT)
    mc = t / "Sigma/mtxel_cor.f90"
    insert(mc, MTXEL_DECL_ANCHOR, MTXEL_DECL)
    insert(mc, MTXEL_ENTRY_ANCHOR, MTXEL_ENTRY, before=True)
    insert(mc, SURVIVE_ANCHOR, SURVIVE_EXPORT)
    wp = t / "Sigma/wpeff.f90"
    insert(wp, WPEFF_DECL_ANCHOR, WPEFF_DECL)
    insert(wp, WPEFF_ANCHOR, WPEFF_EXPORT)


if __name__ == "__main__":
    main(sys.argv[1])
