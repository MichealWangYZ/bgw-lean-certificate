#!/usr/bin/env python3
"""Diagnostic instrumentation of Sigma/mtxel_cor.f90 for E1.2 (write statements only).

    python3 bgw/endpoint/instrument_e1.py TREE      # then `make sigma` in TREE

Exports, to `e1_dump.dat` in the run directory:
  E1G  per mtxel_cor call with in == $E1_BAND: every GPP mode (ig, igp) of the
       q being processed: qk, G(ig), G(igp), I_eps, wtilde, vcoul(igp)
  E1S  per call: qk, in, asxtemp(1:3), achtemp(1:3), achtcor
Every value is printed with ES25.17. No production assignment is changed. This
is a diagnostic used to localise disagreements; the E1 gates compare against
the PRISTINE binary's sigma_hp.log, never against this build.
"""
import pathlib
import sys

SETUP_ANCHOR = "      enddo ! G Loop for GPP Setup\n"
SETUP_EXPORT = """#ifndef CPLX
      call get_environment_variable('E1_BAND', e1_env, status=e1_st)
      e1_band = -1
      if (e1_st == 0) read(e1_env, *) e1_band
      if (in == e1_band) then
        open(792, file='e1_dump.dat', position='append', action='write')
        do e1_ig = 1, ncouls
          write(792,'(A,3ES25.17,6I5,3ES25.17)') 'E1G', qk(1:3), &
            gvec%components(:,isrtrq(e1_ig)), gvec%components(:,isrtrq(igp)), &
            I_eps_array(e1_ig,my_igp), dble(wtilde_array(e1_ig,my_igp)), vcoul(igp)
        enddo
        close(792)
      endif
#endif
"""
DECL_ANCHOR = "  SCALAR :: achstemp, achxtemp, schx, epsggp, I_epsggp, achxtemp_gp, Omega2, wtilde2\n"
DECL = """#ifndef CPLX
  integer :: e1_band, e1_st, e1_ig
  character(len=16) :: e1_env
#endif
"""
END_ANCHOR = "  SAFE_DEALLOCATE(aqsntemp)\n  SAFE_DEALLOCATE(aqsmtemp)\n"
END_EXPORT = """#ifndef CPLX
  if (sig%freq_dep==1) then
    open(792, file='e1_dump.dat', position='append', action='write')
    write(792,'(A,3ES25.17,I5,7ES25.17)') 'E1S', qk(1:3), in, asxtemp(1:3), achtemp(1:3), achtcor
    close(792)
  endif
#endif
"""


def insert(path, anchor, text, before=False, count=None):
    src = path.read_text()
    n = src.count(anchor)
    if n == 0 or (count is not None and n != count):
        raise SystemExit(f"{path}: anchor found {n} times: {anchor!r}")
    new = anchor + text if not before else text + anchor
    path.write_text(src.replace(anchor, new))


def main(tree):
    mc = pathlib.Path(tree) / "Sigma/mtxel_cor.f90"
    insert(mc, DECL_ANCHOR, DECL, count=1)
    insert(mc, SETUP_ANCHOR, SETUP_EXPORT, count=2)
    insert(mc, END_ANCHOR, END_EXPORT, before=True, count=1)


if __name__ == "__main__":
    main(sys.argv[1])
