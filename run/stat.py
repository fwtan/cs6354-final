#!/usr/bin/env python

import os, sys
import cv2, json
import math, time
import subprocess
import numpy as np
import os.path as osp
import pickle
from glob import glob
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--dataset', type=str, default='ALL')
parser.add_argument('--line',    type=int, default=26)

def get_config():
    config, unparsed = parser.parse_known_args()
    return config, unparsed



if __name__ == '__main__':
    cfg, _ = get_config()

    if cfg.dataset is 'ALL':
        file_paths = glob('../outputs/*.txt')
    else:
        file_paths = glob('../outputs/'+ cfg.dataset+'*.txt')

    s = 0
    for x in file_paths:
        y = open(x, 'r').readlines()
        s += float(y[cfg.line].split()[-1])
    print(s/len(file_paths))




    
    
    

