#!/usr/bin/python

import sys, os

import re

from itertools import cycle

import matplotlib
matplotlib.use('PDF')

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D

text_style = dict(horizontalalignment='center', verticalalignment='center',
                  fontsize=12, fontdict={'family': 'monospace'})

from pint import UnitRegistry
ureg = UnitRegistry()

from quantulum import parser

def plotter(ax, data1, list_data2, param_dict):
    """
    Helper function from matplotlib.org/tutorials/introductory/usage.html

    Parameters
    ----------
    ax : Axes
        The axes to draw to

    data1 : array
        The x data

    data2 : array array
        The y data

    param_dict : dict
        Dictionary of kwargs to pass to ax.plot

    Returns
    -------
    out : list
        list of artists added
    """
    out = []
    unfilled_markers = cycle(['x', 'd', 'o', 's'])
    for data2, mm in zip (list_data2, unfilled_markers):
        out.extend(ax.plot(data1, data2, marker=mm, **param_dict))

    return out

def main(argv):
    ninputs = len(argv)
    if ninputs <= 3:
        print "Usage: ", os.path.basename(sys.argv[0]), " <out_file> <seq_time_file> <par_time_file>..."
        sys.exit(-1)
    in_seq_fp = sys.argv[2]
    in_par_fp = sys.argv[3:]
    out_filepath = sys.argv[1]

    in_seq = open(in_seq_fp, "r")

    current_K = None
    current_N = None
    current_S = None
    search_K  = re.compile('^K(\d+)$')
    search_N  = re.compile('(\d+) CORES')
    search_S  = re.compile('benchmarking \w*/(.+)')
    search_T  = re.compile('time\s*(\d+\.\d+ \w+)', re.U)

    seq_data = {}
    par_data = {}
    ## Sequential data
    try:
        for line in in_seq:
            # sK = search_K.search(line)
            # if sK is not None:
            #     current_K = int(sK.group(1))
            #     seq_data[current_K] = {}

            sN = search_N.search(line)
            if sN is not None:
                current_N = int(sN.group(1))
                seq_data[current_N] = {}

            sS = search_S.search(line)
            if sS is not None:
                current_S = int(sS.group(1))
                seq_data[current_N][current_S] = {}

            sT = search_T.search(line)
            if sT is not None:
                tquant = parser.parse(sT.group(1))[0]
                current_T = tquant.value * ureg.parse_expression(tquant.unit.name)
                seq_data[current_N][current_S] = current_T.to('ms').magnitude

        for fp in in_par_fp:
            in_par = open(fp, "r")
            for line in in_par:
                sK = search_K.search(line)
                if sK is not None:
                    current_K = int(sK.group(1))
                    par_data[current_K] = {}

                sN = search_N.search(line)
                if sN is not None:
                    current_N = int(sN.group(1))
                    par_data[current_K][current_N] = {}

                sS = search_S.search(line)
                if sS is not None:
                    current_S = int(sS.group(1))
                    par_data[current_K][current_N][current_S] = None

                sT = search_T.search(line)
                if sT is not None:
                    tquant = parser.parse(sT.group(1))[0]
                    current_T = tquant.value * ureg.parse_expression(tquant.unit.name)
                    par_data[current_K][current_N][current_S] = current_T.to('ms').magnitude
    except AttributeError:
        print "Invalid input files"
        sys.exit(-1)


    speedups_kns = { kk: { nn: {ss: seq_data[nn][ss] / vv
                                  for ss, vv in nn_d.items() }
                              for nn, nn_d in kk_d.items() }
                          for kk, kk_d in par_data.items() }


    ## speedups of +RTS -N
    rtsn_x = [ nn for nn, nn_d in seq_data.items() ]
    rtsn_k2 = [ speedups_kns[2][nn][current_S] for nn in rtsn_x ]
    rtsn_k4 = [ speedups_kns[4][nn][current_S] for nn in rtsn_x ]
    rtsn_k6 = [ speedups_kns[6][nn][current_S] for nn in rtsn_x ]
    rtsn_k8 = [ speedups_kns[8][nn][current_S] for nn in rtsn_x ]

    fig, ax = plt.subplots(1, 1)
    ax.set_ylabel('Speedup', **text_style)
    ax.set_xlabel('+RTS -N', **text_style)

    markers = ['o', 'x', 's', 'h']

    plotter(ax, rtsn_x, [ rtsn_k2, rtsn_k4, rtsn_k6, rtsn_k8 ], {})
    ax.set_title("Size = " + str(current_S), **text_style)
    ax.set_ylim([0, max(rtsn_k2 + rtsn_k4 + rtsn_k6 + rtsn_k8) + 0.5])
    ax.legend(['K2', 'K4', 'K6', 'K8'])

    fig.savefig(out_filepath + "1", dpi=300)
    plt.close(fig)

    ## speedups vs -K, for 4 different sizes

    k_x = range(1, 9)
    sizes_x = [ ss for ss, _ in seq_data[1].items() ]
    nsizes = len(sizes_x) - 1
    sz1 = sizes_x[0]
    sz4 = sizes_x[nsizes]
    sz2 = sizes_x[nsizes / 3]
    sz3 = sizes_x[2 * nsizes / 3]
    k_sz1 = [ speedups_kns[k][4][sz1] for k in k_x ]
    k_sz2 = [ speedups_kns[k][4][sz2] for k in k_x ]
    k_sz3 = [ speedups_kns[k][4][sz3] for k in k_x ]
    k_sz4 = [ speedups_kns[k][4][sz4] for k in k_x ]

    fig, ax = plt.subplots(1, 1)
    ax.set_ylabel('Speedup', **text_style)
    ax.set_xlabel('K', **text_style)

    markers = ['o', 'x', 's', 'h']

    plotter(ax, k_x , [ k_sz1, k_sz2, k_sz3 , k_sz4], {})
    ax.set_title("+RTS -N4 ", **text_style)
    ax.set_ylim([0, max(k_sz1 + k_sz2 + k_sz3 + k_sz4) + 0.5])
    ax.legend([sz1, sz2, sz3, sz4])

    fig.savefig(out_filepath + "2", dpi=300)
    plt.close(fig)

    ## speedups of +RTS -N

# ./plot.py out Base/Measurements/FFT_seq.time K0/Measurements/FFT_par.time
#     K1/Measurements/FFT_par.time K2/Measurements/FFT_par.time
#     K3/Measurements/FFT_par.time K4/Measurements/FFT_par.time
#     K5/Measurements/FFT_par.time K6/Measurements/FFT_par.time
#     K7/Measurements/FFT_par.time K8/Measurements/FFT_par.time
if __name__ == "__main__":
    main(sys.argv)
