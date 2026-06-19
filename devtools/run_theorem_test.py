import os
import sys
import re
import time
import subprocess
from pathlib import Path
from subprocess import PIPE, run

def Out(command):
    result = run(command, stdout=PIPE, stderr=PIPE, universal_newlines=True, shell=True, encoding='utf-8')
    return result.stdout

def LaunchTest(prover_name, command_line, succes, f, memory_limit=None, failure=None):
    output = Out(command_line).encode('utf-8', errors='ignore').decode(errors='ignore')
    res = False
    if re.search(succes, output):
        f.write(f"Found proof. Good job, {prover_name} !\n")
        res = True
    else:
        f.write("Proof not found\n")
    return res

def set_cpu_freq(freq_khz):
    # Define CPU Speed 
    cmd = f"sudo cpupower frequency-set -g performance -u {freq_khz} -d {freq_khz}"
    result = subprocess.run(cmd, shell=True, stdout=PIPE, stderr=PIPE, universal_newlines=True)
    if result.returncode != 0:
        print("Error. sudo ?.")
        print(result.stderr)
    else:
        print(f"CPU Speed is {int(freq_khz)/1000} MHz.")

if len(sys.argv) < 3:
    print(f"python3 {sys.argv[0]} problem_folder timeout goeland_options")
else:
    NB_CORES = 4
    CORES = ",".join(str(i) for i in range(NB_CORES))
    FREQ_KHZ = 2000000  # 2.0 GHz

    set_cpu_freq(FREQ_KHZ)
    print(f"{NB_CORES} cores are working")

    folder = sys.argv[1]
    folder_split = folder.split("/")
    folder += "/"
    entries = os.listdir(folder)
    timeout = sys.argv[2]
    total = len(entries)

    filename = ""
    for i in range (0,sys.maxsize) : 
        a  = Path("resultV1_" + str(i) + ".txt")
        if not a.exists(): 
            filename = a 
            break

    with open(filename, "w") as f:
        milli_sec_deb = int(round(time.time() * 1000))
        cpt = 0
        for index, file in enumerate(entries):
            f.write(f"Problem {index+1}/{len(entries)} : {folder+file}\n")
            command = (
                f"taskset -c {CORES} env GOMAXPROCS={NB_CORES} "
                f"timeout {timeout} ../src/_build/goeland -dt "
                + " ".join(sys.argv[4:]) + " " + folder + file
            )
            if LaunchTest("Goéland", command, "% RES : VALID", f, None, "% RES : NOT VALID"):
                cpt += 1
        milli_sec_fin = int(round(time.time() * 1000))
        timer = milli_sec_fin - milli_sec_deb
        f.write(f"Number of problems solved : {cpt}/{total}\n")
        f.write(f"Execution Time : {timer}ms\n")
