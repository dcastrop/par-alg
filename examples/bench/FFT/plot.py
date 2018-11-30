#!/usr/bin/python

import sys, os

import matplotlib
matplotlib.use('PDF')

import matplotlib.pyplot as plt
import numpy as np


def plotter(ax, data1, data2, param_dict):
    """
    Helper function from matplotlib.org/tutorials/introductory/usage.html

    Parameters
    ----------
    ax : Axes
        The axes to draw to

    data1 : array
        The x data

    data2 : array
        The y data

    param_dict : dict
        Dictionary of kwargs to pass to ax.plot

    Returns
    -------
    out : list
        list of artists added
    """
    out = ax.plot(data1, data2, **param_dict)
    return out

def main(argv):
    if len(argv) <= 1:
        print "Usage: ", os.path.basename(sys.argv[0]), " <file>"
        sys.exit(-1)

    outFile = sys.argv[1]

    data1, data2, data3, data4 = np.random.randn(4, 100)
    fig, ax = plt.subplots(1, 1)
    plotter(ax, data1, data2, {'marker' :  'x'})
    plt.savefig(outFile)

if __name__ == "__main__":
    main(sys.argv)
