import subprocess
import os.path

dss = ['List', 'HashMap', 'NMTree', 'BonsaiTree']
mms = ['EBR', 'PEBR', 'NR']
ns = [0, 1, 2]
ts = list(map(str, [1] + list(range(5, 76, 5))))
cs = [1, 4]

if os.path.exists('.git'):
    subprocess.run(['git', 'submodule', 'update', '--init', '--recursive'])
subprocess.run(['cargo', 'build', '--release'])

run_cmd = ['./target/release/pebr-benchmark', '-i10', '-s1']


def opts(ds, mm, t, c=1, n=0):
    return ['-d', ds, '-m', mm, '-t', t, '-n', str(n), '-c', str(c)]

# througput
for ds in dss:
    for mm in mms:
        for n in ns:
            for c in cs:
                # meaningless
                if mm == 'NR' and (n != 0 or c != 1):
                    continue
                for t in ts:
                    cmd = run_cmd + opts(ds, mm, t, c=c, n=n)
                    # print(' '.join(cmd))
                    subprocess.run(cmd)