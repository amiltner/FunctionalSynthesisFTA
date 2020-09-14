#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
from os.path import splitext, join
import subprocess
import sys
import time
import matplotlib
import matplotlib as mpl
mpl.use('pgf')
import numpy as np
import matplotlib.pyplot as plt

plt.rc('font', size=10)
plt.rc('legend', fontsize=10)

generated_graphs_base = "generated-graphs/"
transformed_data_base = "transformed-data/"

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)


def print_usage(args):
    print("Usage: {0} <file1>".format(args[0]))

def retrieve_csv(filename):
    csv_rows = []
    with open(filename, 'rb') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            csv_rows.append(row)
    return csv_rows

def project_column_from_csv(csv_obj, col_name):
    return [r[col_name] for r in csv_obj]

def count_real_vals(csv_obj, col_name):
    col = project_column_from_csv(csv_obj, col_name)
    return len([val for val in col if val != "[-1]"])

def write_to_filename(filename, s):
    with open(filename, "wb") as f:
        f.write(s)

def generate_examples_required_graph(input_csv):
    nm_count = count_real_vals(input_csv,"NM")
    fc_count = count_real_vals(input_csv,"FC")
    no_skip_count = count_real_vals(input_csv,"NoSkip")
    no_require_count = count_real_vals(input_csv,"NoRequire")
    constcostcc_count = count_real_vals(input_csv,"ConstCostCC")
    print(nm_count)
    print(fc_count)
    print(no_skip_count)
    print(no_require_count)
    print(constcostcc_count)

    ind = np.arange(5)
    width = 0.35

    fig, ax = plt.subplots()

    rects1 = ax.bar(ind, [nm_count,fc_count,constcostcc_count,no_skip_count,no_require_count], width, color='#ffffb3', align='center')

    ax.set_ylabel('Benchmarks\nCompleted')
    ax.set_xlabel('Run Mode')
    ax.set_xticks(ind)
    ax.set_xticklabels(["\\textbf{Any}","\\textbf{FL}","\\textbf{DC}","\\textbf{NS}","\\textbf{NR}"])

    fig = plt.figure(3,tight_layout=True)
    #ax.step([-.5,4.5],[48.1,48.1],label="Benchmark Count",linestyle=":",
    #        linewidth=1, dashes=(1,1))

    plt.tick_params(
                axis='x',          # changes apply to the x-axis
                    which='both',      # both major and minor ticks are affected
                        bottom='off',      # ticks along the bottom edge are off
                            top='off') # labels along the bottom edge are off
    fig.set_figheight(1)
    fig.set_figwidth(5)

    fig.savefig(generated_graphs_base + "metrics_importance.eps", bbox_inches='tight')

def generate_compositional_lenses_graph(input_csv):
    zero_count_ind = 0
    one_to_five_count_ind = 1
    six_to_ten_count_ind = 2
    eleven_to_fifteen_count_ind = 3
    sixteen_to_twenty_count_ind = 4

    zero_count_text = "0"
    one_to_five_count_text = "1"
    six_to_ten_count_text = "2"
    eleven_to_fifteen_count_text = "3"
    sixteen_to_twenty_count_text = "4"
    ind_to_text = [zero_count_text,
                   one_to_five_count_text,
                   six_to_ten_count_text,
                   eleven_to_fifteen_count_text,
                   sixteen_to_twenty_count_text]

    experimental_values = [0,0,0,0,0,]
    determinizing_values = [0,0,0,0,0,]

    def add_to_correct_group(count_values, n):
        if n < 0.0:
            raise Exception("SOMETHING WENT WRONG")
        if n == 0.0:
            count_values[zero_count_ind] = count_values[zero_count_ind]+1
        elif n == 1.0:
            count_values[one_to_five_count_ind] = count_values[one_to_five_count_ind]+1
        elif n == 2.0:
            count_values[six_to_ten_count_ind] = count_values[six_to_ten_count_ind]+1
        elif n == 3.0:
            count_values[eleven_to_fifteen_count_ind] = count_values[eleven_to_fifteen_count_ind]+1
        elif n == 4.0:
            count_values[sixteen_to_twenty_count_ind] = count_values[sixteen_to_twenty_count_ind]+1
        else:
            raise Exception("SOMETHING WENT WRONG")

    vals = project_column_from_csv(input_csv, "CompositionalLensesUsed")
    for example_num in vals:
        add_to_correct_group(experimental_values, float(example_num))

    ind = np.arange(5)
    width = 0.35

    fig, ax = plt.subplots()

    rects1 = ax.bar(ind, experimental_values, width, color='#ffffb3', align='center')

    ax.set_ylabel('Benchmark Count')
    ax.set_xlabel('Subtasks Specified')
    ax.set_title("Subtasks Specified During Compositional Synthesis")
    ax.set_xticks(ind)
    ax.set_xticklabels(ind_to_text)

    fig = plt.figure(3,tight_layout=True)
    fig.set_figheight(1.8)
    fig.set_figwidth(5)

    fig.savefig(generated_graphs_base + "compositional.eps", bbox_inches='tight')

def generate_uninferred_expansions_graph(input_csv):
    zero_count_ind = 0
    one_to_five_count_ind = 1
    six_to_ten_count_ind = 2
    eleven_to_fifteen_count_ind = 3
    sixteen_to_twenty_count_ind = 4
    over_twenty_count_ind = 5

    zero_count_text = "0"
    one_count_text = "1"
    two_count_text = "2"
    three_count_text = "3"
    four_count_text = "4"
    ind_to_text = [zero_count_text,
                   one_count_text,
                   two_count_text,
                   three_count_text,
                   four_count_text]

    uninferred_values = [0,0,0,0,0,]
    unforced_values = [0,0,0,0,0,]

    def add_to_correct_group(count_values, n):
        if n == 0.0:
            count_values[zero_count_ind] = count_values[zero_count_ind]+1
        elif n == 1.0:
            count_values[one_to_five_count_ind] = count_values[one_to_five_count_ind]+1
        elif n == 2.0:
            count_values[six_to_ten_count_ind] = count_values[six_to_ten_count_ind]+1
        elif n == 3.0:
            count_values[eleven_to_fifteen_count_ind] = count_values[eleven_to_fifteen_count_ind]+1
        elif n == 4.0:
            count_values[sixteen_to_twenty_count_ind] = count_values[sixteen_to_twenty_count_ind]+1
        else:
            raise Exception("SOMETHING WENT WRONG")

    total_exps = project_column_from_csv(input_csv, "ExpansionsPerformedNoLensContext")
    forced_exps = project_column_from_csv(input_csv, "ExpansionsForcedNoLensContext")
    inferred_exps = project_column_from_csv(input_csv, "ExpansionsInferredNoLensContext")
    total_and_inferred = zip(total_exps, inferred_exps)
    total_and_forced = zip(total_exps, forced_exps)
    for (total_exp,forced_exp) in total_and_forced:
        add_to_correct_group(unforced_values, float(total_exp)-float(forced_exp))
    for (total_exp,inferred_exp) in total_and_inferred:
        add_to_correct_group(uninferred_values, float(total_exp)-float(inferred_exp))

    ind = np.arange(5)
    width = 0.35

    fig, ax = plt.subplots()

    rects1 = ax.bar(ind, uninferred_values, width, color='#ffffb3', align='center')
    rects2 = ax.bar(ind+width, unforced_values, width, color='#998ec3', align='center')

    ax.set_ylabel('Benchmark Count')
    ax.set_xlabel('Expansions Not Inferred')
    ax.set_title("Number of Benchmarks with Uninferred Expansions")
    ax.set_xticks(ind + width / 2)
    ax.set_xticklabels(ind_to_text)

    l = ax.legend((rects1[0],rects2[0]),("NoCS","NoFPE"))
    plt.setp(l.texts, weight='bold')

    fig = plt.figure(2,tight_layout=True)
    fig.set_figheight(1.8)
    fig.set_figwidth(5)

    fig.savefig(generated_graphs_base + "uninferred.eps", bbox_inches='tight')

def generate_examplecount_vs_tasks_graph(input_csv):
    fig, ax = plt.subplots()

    def create_step_plot(colname, outputname,style,width):
        col_vals = [float(x) for x in project_column_from_csv(input_csv, colname) if x != "-1"]
        col_vals_and_endpoints = col_vals + [0,10]
        x_vals = sorted([x for x in set(col_vals_and_endpoints)])
        x_count_dict = {key: 0 for key in x_vals}
        for val in col_vals:
            x_count_dict[val] = x_count_dict[val]+1
        x_completed_counts = []
        acc = 0
        for val in x_vals:
            acc = acc + x_count_dict[val]
            x_completed_counts.append(acc)
        x_completed_counts = [0] + x_completed_counts[:len(x_completed_counts)-1]

        if (style != '-'):
            ax.step(x_vals,x_completed_counts,label=outputname,linestyle=style,linewidth=width, dashes=(5,1))
        else:
            ax.step(x_vals,x_completed_counts,label=outputname,linestyle=style,linewidth=width)

    normal_size = 2
    full_size = 3

    create_step_plot("ExamplesCount","Example Number",'-',full_size)

    ax.set_ylabel('Benchmarks Definable')
    ax.set_xlabel('Example Count')
    ax.set_title("Example Count vs\nBenchmarks Definable")

    fig = plt.figure(6,tight_layout=True)
    fig.set_figheight(1.5)
    fig.set_figwidth(2.5)
       
    fig.savefig(generated_graphs_base + "examplesused.eps", bbox_inches='tight')

def generate_specsize_vs_tasks_graph(input_csv):
    fig, ax = plt.subplots()

    def create_step_plot(colname, outputname,style,width):
        col_vals = [float(x) for x in project_column_from_csv(input_csv, colname) if x != "-1"]
        col_vals_and_endpoints = col_vals + [0,900]
        x_vals = sorted([x for x in set(col_vals_and_endpoints)])
        x_count_dict = {key: 0 for key in x_vals}
        for val in col_vals:
            x_count_dict[val] = x_count_dict[val]+1
        x_completed_counts = []
        acc = 0
        for val in x_vals:
            acc = acc + x_count_dict[val]
            x_completed_counts.append(acc)
        x_completed_counts = [0] + x_completed_counts[:len(x_completed_counts)-1]

        if (style != '-'):
            ax.step(x_vals,x_completed_counts,label=outputname,linestyle=style,linewidth=width, dashes=(5,1))
        else:
            ax.step(x_vals,x_completed_counts,label=outputname,linestyle=style,linewidth=width)

    normal_size = 2
    full_size = 3

    create_step_plot("SpecSize","Regular Expression Size",'-',full_size)

    ax.set_ylabel('Benchmarks Definable')
    ax.set_xlabel('AST Count')
    ax.set_title("AST Count vs\nBenchmarks Definable")

    fig = plt.figure(5,tight_layout=True)
    fig.set_figheight(1.5)
    fig.set_figwidth(2.5)
       
    fig.savefig(generated_graphs_base + "specsizes.eps", bbox_inches='tight')

def can_be_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def generate_time_vs_tasks_graph(input_csv):
    fig, ax = plt.subplots()

    def create_step_plot(colname, outputname,style,width):
        col_vals = [float(x) for x in project_column_from_csv(input_csv, colname) if can_be_float(x)]
        col_vals_and_endpoints = col_vals + [0,1800]
        x_vals = sorted([x for x in set(col_vals_and_endpoints)])
        x_count_dict = {key: 0 for key in x_vals}
        for val in col_vals:
            x_count_dict[val] = x_count_dict[val]+1
        x_completed_counts = []
        acc = 0
        for val in x_vals:
            acc = acc + x_count_dict[val]
            x_completed_counts.append(acc)
        x_completed_counts = [0] + x_completed_counts[:len(x_completed_counts)-1]
        if (style != '-'):
            ax.step(x_vals,x_completed_counts,label=outputname,linestyle=style,linewidth=width, dashes=(5,1))
        else:
            ax.step(x_vals,x_completed_counts,label=outputname,linestyle=style,linewidth=width)

    normal_size = 2
    full_size = 3

    #ax.step([0,60],[48.1,48.1],label="Benchmark Count",linestyle=":",
    #        linewidth=1, dashes=(1,1))
    create_step_plot("MythTime","Hanoi",'-',normal_size)
    create_step_plot("SRPTime","Hanoi$_{-SRC}$",':',normal_size)
    create_step_plot("CLPTime","Hanoi$_{-CLC}$",'-',normal_size)
    create_step_plot("ConjStrTime","$\wedge$ Str",':',normal_size)
    create_step_plot("LAStrTime","LA",'-',normal_size)
    create_step_plot("ThirtyTime","OneShot",':',normal_size)

    ax.set_ylabel('Benchmarks\nCompleted')
    ax.set_xlabel('Time (s)')

    l = ax.legend(bbox_to_anchor=(1,1.4),borderaxespad=0,ncol=3)
    #l = ax.legend(bbox_to_anchor=(1.6,1),borderaxespad=0)
    plt.setp(l.texts) 

    plt.xlim(0,1800)
    plt.yticks(np.arange(0, 25.1, 5))

    fig = plt.figure(1,tight_layout=True)
    fig.set_figheight(1.75)
    fig.set_figwidth(4)

    fig.savefig(generated_graphs_base + "times.eps", bbox_inches='tight')

def generate_benchmark_count(input_csv):
    write_to_filename(transformed_data_base + "benchmark-count.txt", str(len(input_csv)))

def generate_multiple_of_five_number_of_seconds_synthesized_under(input_csv):
    times = project_column_from_csv(input_csv,"ComputationTime")
    maxtime = max([float(x)/1000 for x in times])
    num = 0.0
    while (num < maxtime):
        num = num+5.0
    write_to_filename(transformed_data_base + "multiple-of-five-number-of-seconds-synthesized-under.txt", str(int(num)))

def generate_number_augeas(input_csv):
    names = project_column_from_csv(input_csv,"Test")
    augeasnames = [x for x in names if x.startswith("aug")]
    write_to_filename(transformed_data_base + "augeas-count.txt", str(len(augeasnames)))

def generate_min_lens_size(input_csv):
    sizes_strings = project_column_from_csv(input_csv,"LensSize")
    sizes = [int(x) for x in sizes_strings]
    write_to_filename(transformed_data_base + "min_lens_size.txt", str(min(sizes)))

def generate_min_lens_size(input_csv):
    sizes_strings = project_column_from_csv(input_csv,"LensSize")
    sizes = [int(x) for x in sizes_strings]
    write_to_filename(transformed_data_base + "max_lens_size.txt", str(max(sizes)))

def generate_median_expands_forced(input_csv):
    sizes_strings = project_column_from_csv(input_csv,"ExpansionsForcedNoLensContext")
    exps = [int(x) for x in sizes_strings]
    write_to_filename(transformed_data_base + "median_expansions_forced.txt", str(int(np.median(exps))))

def generate_maximum_expands_forced(input_csv):
    sizes_strings = project_column_from_csv(input_csv,"ExpansionsForcedNoLensContext")
    exps = [int(x) for x in sizes_strings]
    write_to_filename(transformed_data_base + "maximum_expansions_forced.txt", str(int(max(exps))))

def main(args):
    if len(args) == 2:
        bijective_filepath = args[1]
        #symmetric_filepath = args[2]
        bijective_csv = retrieve_csv(bijective_filepath)
        #symmetric_csv = retrieve_csv(symmetric_filepath)
        #ensure_dir(generated_graphs_base)
        #ensure_dir(transformed_data_base)
        #generate_uninferred_expansions_graph(input_csv)
        #generate_compositional_lenses_graph(input_csv)
        ensure_dir(generated_graphs_base)
        generate_time_vs_tasks_graph(bijective_csv)
        #generate_time_vs_tasks_graph_vs_bijective(bijective_csv)
        #generate_examples_required_graph(symmetric_csv)
        #generate_benchmark_count(input_csv)
        #generate_multiple_of_five_number_of_seconds_synthesized_under(input_csv)
        #generate_number_augeas(input_csv)
        #generate_min_lens_size(input_csv)
        #generate_median_expands_forced(input_csv)
        #generate_maximum_expands_forced(input_csv)
        #generate_specsize_vs_tasks_graph(input_csv)
        #generate_examplecount_vs_tasks_graph(input_csv)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
