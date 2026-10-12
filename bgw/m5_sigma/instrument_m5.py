#!/usr/bin/env python3
"""BGW-M5 instrumentation: the BGW-M4-R1 exports plus the GPP kernel's
per-mode SX/CH values for one consumer (ig, igp).

    M5_IG=2 M5_IGP=1 sigma.real.x ...     (after `python3 instrument_m5.py TREE`)

Write statements only, plus one extra assignment to a NEW variable
(`m5_ssx0 = ssx`, the value before the `sexcut` clamp). Every production
assignment is left in place. The M4-R1 records are emitted unchanged, so the
M4-R1 subset of this run's dump can be compared with the committed M4-R1 dump.
"""
import importlib.util
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
_s = importlib.util.spec_from_file_location("r1", HERE.parent / "m4_gpp" / "instrument_r1.py")
r1 = importlib.util.module_from_spec(_s)
_s.loader.exec_module(r1)

OPEN = r1.OPEN
B = r1.B

DECL_ANCHOR = "    SCALAR :: ssx, sch, ssxt, scht, schtt\n"
DECL = """#ifndef CPLX
    SCALAR :: m5_ssx0
    integer :: m5_ig, m5_igp, m5_st
    integer(8) :: m5_b
    character(len=16) :: m5_env
#endif
"""

PRECLAMP_ANCHOR = "            ssxcutoff = sig%sexcut*abs(I_eps_array(ig,my_igp))\n"
PRECLAMP = """#ifndef CPLX
            m5_ssx0 = ssx
#endif
"""

CLAMP_ANCHOR = "            if (abs(ssx) .gt. ssxcutoff .and. wxt .lt. 0.0d0) ssx=0.0d0\n"
EXPORT = f"""#ifndef CPLX
            ! BGW-M5: one consumer mode's SX/CH operands and values, occupied bands.
            call get_environment_variable('M5_IG', m5_env, status=m5_st)
            m5_ig = -1
            if (m5_st == 0) read(m5_env, *) m5_ig
            call get_environment_variable('M5_IGP', m5_env, status=m5_st)
            m5_igp = -1
            if (m5_st == 0) read(m5_env, *) m5_igp
            if (ig == m5_ig .and. igp == m5_igp) then
              {OPEN}
              write(791,'(A,8(1X,I0),12(1X,I0))') 'SGP', in, il, n1, n1true, iw, &
                my_igp, indigp, ig, &
                {B.format('wxt')}, {B.format('e_lk')}, {B.format('e_n1kq')}, &
                {B.format('dble(wtilde)')}, {B.format('aimag(wtilde)')}, &
                {B.format('wtilde2')}, {B.format('Omega2')}, &
                {B.format('I_eps_array(ig,my_igp)')}, {B.format('dble(wdiff)')}, &
                {B.format('dble(delw)')}, {B.format('delwr')}, {B.format('wdiffr')}
              write(791,'(A,2(1X,I0),11(1X,I0))') 'SGQ', n1, iw, &
                {B.format('sch')}, {B.format('m5_ssx0')}, {B.format('ssx')}, &
                {B.format('ssxcutoff')}, {B.format('aqsntemp(ig,n1)')}, &
                {B.format('aqsmtemp(igp,n1)')}, {B.format('vcoul(igp)')}, {B.format('occ')}, &
                {B.format('sig%sexcut')}, {B.format('limittwo')}, {B.format('limitone')}
              close(791)
            endif
#endif
"""


def main(tree):
    r1.main(tree)
    mc = pathlib.Path(tree) / "Sigma/mtxel_cor.f90"
    r1.insert(mc, DECL_ANCHOR, DECL)
    r1.insert(mc, PRECLAMP_ANCHOR, PRECLAMP, before=True)
    r1.insert(mc, CLAMP_ANCHOR, EXPORT)


if __name__ == "__main__":
    main(sys.argv[1])
