#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## cactus.py
##
##  Created on: Jun 05, 2015
##      Author: Alexey S. Ignatiev
##      E-mail: aignatiev@ciencias.ulisboa.pt
##

#
#==============================================================================
import json
import matplotlib.pyplot as plt
from matplotlib import __version__ as mpl_version
import math
import numpy as np
import os
from plot import Plot
import six


#
#==============================================================================
class Cactus(Plot, object):
    """
        Cactus plot class.
    """

    def __init__(self, options):
        """
            Cactus constructor.
        """

        super(Cactus, self).__init__(options)

        with open(self.def_path, 'r') as fp:
            self.linestyles = json.load(fp)['cactus_linestyle']
            self.instance = options['plot_type'] == 'instance'

    def create(self, data):
        """
            Does the plotting.
        """
        import sys
        # data = sorted(data, key=lambda x: int(x[5]))

        # making lines
        coords = []
        insts = set()
        for d in data:
            coords.append(np.arange(1, len(d[1]) + 1))  # xs (separate for each line)
            if self.instance:
                vals = [ x for x in sorted(d[1], key = lambda x: int(x[0]) if self.instance else x[1]) ]
                coords.append(np.array([ x[1] for x in vals]))
                insts |= { x[0] for x in vals }
            else:
                coords.append(np.array(sorted([ x[1] for x in d[1] ])))
        lines = plt.plot(*coords, zorder=3)

        # setting line styles
        if self.byname == False:  # by default, assign fist line to best tool
            lmap = lambda i: i
        else:  # assign line styles by tool name
            tnames = [(d[4], i) for i, d in enumerate(data)]
            tnames.sort(key=lambda pair: pair[0])
            tmap = {tn[1]: i for i, tn in enumerate(tnames)}
            lmap = lambda i: tnames[i]
            lmap = lambda i: data[i][4]


        for i, l in enumerate(lines):
            plt.setp(l, **self.linestyles[lmap(i) % len(self.linestyles)])

        # turning the grid on
        if not self.no_grid:
            plt.grid(True, color=self.grid_color, ls=self.grid_style, lw=self.grid_width, zorder=1)

        # axes limits
        plt.xlim(self.x_min, self.x_max if self.x_max else math.ceil(max([d[2] for d in data]) / float(100)) * 100)
        plt.ylim(self.y_min, self.y_max if self.y_max else self.timeout)

        # axes labels
        if self.x_label:
            plt.xlabel(self.x_label)
        else:
            plt.xlabel('instances')

        if self.y_label:
            plt.ylabel(self.y_label)
        else:
            plt.ylabel('CPU time (s)')

        # choosing logarithmic scales if needed
        ax = plt.gca()
        if self.x_log:
            ax.set_xscale('log')
        if self.y_log:
            ax.set_yscale('log')

        # setting ticks
        # xtick_labels=sorted([ int(x[0]) for x in vals ])
        # xtick_labels=sorted({ int(x[0]) for x in d[1] for d in data })
        # plt.xticks(ticks=np.arange(self.x_min, self.x_max + 1, 2), labels=xtick_labels)
        # plt.xticks(ticks=np.arange(1, len(xtick_labels) + 1), labels=xtick_labels)
        # plt.xticks(np.arange(self.x_min, self.x_max + 1, 2))
        # if not self.y_log:
        #     # plt.yticks(list(plt.yticks()[0]) + [self.timeout])
        #     ax.set_yticks(range(0, 2 * (int(self.y_max) if self.y_max else int(self.timeout)), 200))

        # setting ticks font properties
        # set_*ticklables() seems to be not needed in matplotlib 1.5.0
        if float(mpl_version[:3]) < 1.5:
            ax.set_xticklabels(ax.get_xticks(), self.f_props)
            ax.set_yticklabels(ax.get_yticks(), self.f_props)

        strFormatter = plt.FormatStrFormatter('%d')
        logFormatter = plt.LogFormatterMathtext(base=10)
        if self.instance:
            xtick_labels=sorted(list(int(i) for i in insts))
            ax.set_xticks(ticks=np.arange(1, len(xtick_labels) + 1), labels=xtick_labels)
        else:
            ax.xaxis.set_major_formatter(strFormatter if not self.x_log else logFormatter)
        ax.yaxis.set_major_formatter(strFormatter if not self.y_log else logFormatter)

        # making the legend
        if self.lgd_loc != 'off':
            #lgtext = [d[0] for d in sorted(data, key = lambda d: "y" if "SR" in d[0] else "z" if "PBLib" in d[0] else d[0] )]
            #lgtext = [d[0] for d in sorted(data, key = lambda d: d[0])]
            lgtext = [d[0] for d in sorted(data, key = lambda d: d[4])]
            lines = [l[1] for l in sorted(enumerate(lines), key = lambda i_line: lmap(i_line[0]))]
            lg = ax.legend(lines, lgtext, ncol=self.lgd_ncol, loc=self.lgd_loc, fancybox=self.lgd_fancy, shadow=self.lgd_shadow if self.lgd_alpha == 1.0 else False)
            fr = lg.get_frame()
            fr.set_lw(1)
            fr.set_alpha(self.lgd_alpha)
            fr.set_edgecolor('black')

        # setting frame thickness
        for i in six.itervalues(ax.spines):
            i.set_linewidth(1)

        plt.savefig(self.save_to, bbox_inches='tight', transparent=self.transparent)

        # save legend separately
        import pylab
        fig = pylab.figure()
        figlegend = pylab.figure(figsize=(3,2))
        ax = fig.add_subplot(111)
        lines = ax.plot(range(10), pylab.randn(10), range(10), pylab.randn(10))
        figlegend.legend(lines, ('one', 'two'), 'center')
        #fig.show()
        #figlegend.show()
        figlegend.savefig('legend.png')
