#!/usr/bin/python
# -*- coding: utf-8 -*-

# used libraries
import os, signal, subprocess, time
import sys, shutil, random
from time import clock
import copy
import data_instance

numCores=2

# setup tmp files
tmpDir="/tmp/"

MAX_READY_NUM = 32

verb=1

pids=set()
pidsseed={}
seeds=set()

str_instances=[
    "/mirror/sat/tb/ibm-2002-05r-k90.cnf",
    "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-11r1-k45.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/goldb-heqc-frg2mul.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/goldb-heqc-desmul.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/een-pico-prop01-75.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/een-pico-prop05-50.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/een-tip-sat-nusmv-t5.B.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/een-tip-sat-nusmv-tt5.B.cnf",
    # "/mirror/sat/tb/sat_tb_2006/SAT-Race-Benchmarks/een-tip-uns-nusmv-t5.B.cnf",
    # "/mirror/sat/tb/ibm-2002-05r-k90.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-11r1-k45.cnf",
    # "/mirror/sat/tb/ibm-2002-05r-k90.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-11r1-k45.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-05r-k90.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-11r1-k45.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-05r-k90.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
    # "/mirror/sat/tb/ibm-2002-11r1-k45.cnf",
    # "/mirror/sat/tb/ibm-2002-07r-k100.cnf",
]

str_instances = data_instance.str_instances

num_cpus_used = 0

class queue(object):
    def __init__(self):
        self.data = []

    def __repr__(self):
        s = 'queue ['
        for i, l in enumerate(self.data):
            if i%4 == 0:
                s += '\n\t'
            if i != len(self.data):
                s += str(l)+', '
            else:
                s += str(l)
        s += ']'
        return s

    def pop(self):
        if len(self.data) == 0:
            return None
        l = self.data[0]
        del self.data[0]
        return l

    def push(self, l):
        self.data += [l]
        return l

    def __len__(self):
        return len(self.data)


solverlist = []

instances = []

firsttaskqueue = queue()  # 初次任务队列
nexttaskqueue = queue()  # 非初次任务队列

readyqueue = queue()     # 就绪队列
runninglist = {}         # 运行列表 pid:task pid到task的映射，

insts_solved = []      # 实例状态队列



class Solver(object):
    def __repr__(self):
        return "solver%d %s" % (self.sid, self.name)

    def __init__(self, name, command, sid):
        self.name = name
        self.command = command
        self.sid = sid

        self.pid = 0
        self.inst_num = 0
        self.fnameout = ""

        self.solverprocess = None

        self.time_limit_str = "-cpu-lim="
        self.time_limit = 0.0
        self.result = "unknown"     # sat, unsat, indeterminate
        self.cputime = 0.0

    def start(self, num, limit_time):
        tmpFile=tmpDir + "sat_inst%04d_s%02d" % (num, self.sid)
        self.time_limit = limit_time
        print ""
        print "c starting inst" + str(num)
        print '\tsolver', self.sid, self.name, self.command, self.time_limit_str + str(limit_time)
        print '\tinst', num, str_instances[num]
        # print "c writing to files " + tmpFile +".out .err"

        # start probSAT
        satCallString= self.command + ' ' + str_instances[num] + ' ' + self.time_limit_str + str(limit_time)
        args = satCallString.split()	# split the actual command line
        # print satCallString
        # print "c calling " + str(args)
        p = subprocess.Popen(args, stdout=open(tmpFile + ".out","w"), stderr=open(tmpFile + ".err","w"), preexec_fn=os.setpgrp)
        self.solverprocess = p
        self.pid = p.pid
        self.inst_num = num
        self.fnameout = tmpFile + ".out"
        # print "c started SAT instance with PID" + str(p.pid)
        global num_cpus_used
        num_cpus_used += 1
        return p

    def stop(self):
        # print 'send kill signal to pid %d' % self.pid
        # self.solverprocess.send_signal(signal.SIGINT)
        # os.kill(self.pid, signal.SIGINT)
        # os.kill(self.pid, 15)
        flag = self.solverprocess.poll()   # 查询程序状态，程序正在运行时会返回None
        if flag is None:
            print 'kill child process pid %d' % self.pid
            self.solverprocess.kill()

        # 统一在os.wait()后进行num_cpus_used减少的处理
        # global num_cpus_used
        # num_cpus_used -= 1

    def get_result(self):
        f = open(self.fnameout, 'r')
        for l in f.readlines():
            l = l.strip()
            if "UNSATISFIABLE" in l:
                self.result = 'unsat'
                print '\t', l
            elif "SATISFIABLE" in l:
                self.result = 'sat'
                print '\t', l
            elif "CPU time" in l:
                t = l.strip().split()
                self.cputime = float(t[-2])
                print '\t', l
        if self.result != 'sat' and self.result != 'unsat':
            self.result = 'time_out'
            self.cputime = self.time_limit + 1
        return self.result

class Task(object):
    def __init__(self, solver_id, inst_id, limit_time):
        self.taskstate = "ready"  # 'ready', 'run', 'stop'
        self.solver_id = solver_id
        self.inst_id = inst_id
        self.limit_time = limit_time
        self.inststate = None

        self.inst_name = str_instances[inst_id]

        self.solver = copy.deepcopy(solverlist[solver_id])

    def __repr__(self):
        return "inst%d solver%d %s" % (self.inst_id, self.solver_id, self.taskstate)

    def start(self):
        p = self.solver.start(self.inst_id, self.limit_time)
        global runninglist
        runninglist[p.pid] = self
        self.taskstate = 'run'
        return p

    def stop(self):
        if self.taskstate == 'stop':
            return
        self.taskstate = 'stop'
        self.solver.stop()
        global runninglist
        del runninglist[self.solver.pid]

    def get_result(self):
        return self.solver.get_result()


class InstState(object):
    def __init__(self, inst_id):
        self.run_state = 0   # 0, 1, 2, 3
        self.cnt_runs_cur_state = 0
        self.inst_id = inst_id

        self.inst_name = str_instances[inst_id]
        self.tasks = []

        self.result = 'unsolved'

        # self.limit_time = [100, 400, 1000, 5000]
        self.MAX_STATE_NUM = 1
        self.LIMIT_TIME = [100, 4, 16, 100]
        self.LIMIT_TASKS_NUM = [len(solverlist), 2, 4, 12]

    def __repr__(self):
        return "inst%d %s state%d cnt%d" % (self.inst_id, self.result, self.run_state, self.cnt_runs_cur_state)

    def add_task(self):
        if self.result != 'unsolved':
            if verb > 2:
                print 'inst already solved', self
            return None
        if self.run_state >= self.MAX_STATE_NUM:
            if verb > 2:
                print 'inst have used all time slices', self
            return None
        self.cnt_runs_cur_state = 0
        ts = []
        for i in xrange(self.LIMIT_TASKS_NUM[self.run_state]):
            t = Task(i, self.inst_id, self.LIMIT_TIME[self.run_state])
            t.inststate = self
            self.tasks += [t]
            ts += [t]
        self.run_state += 1
        if verb > 2:
            print "----add_task", self, t
        return ts

    def is_last_task(self):
        return self.run_state >= self.MAX_STATE_NUM or self.cnt_runs_cur_state == self.LIMIT_TASKS_NUM[3]

    def is_last_cur_state(self):
        return self.cnt_runs_cur_state == self.LIMIT_TASKS_NUM[self.run_state]

    def stop_all_task(self):
        for t in self.tasks:
            t.stop()


def update_readyqueue():
    """更新就绪队列，选择firsttaskqueue和nexttaskqueue中的任务"""
    global readyqueue
    global firsttaskqueue
    global nexttaskqueue

    # 优先选择firsttaskqueue
    while(len(readyqueue) < MAX_READY_NUM and len(firsttaskqueue) > 0):
        t = firsttaskqueue.pop()
        readyqueue.push(t)

    # 再选择firsttaskqueue
    while(len(readyqueue) < MAX_READY_NUM and len(nexttaskqueue) > 0):
        t = nexttaskqueue.pop()
        readyqueue.push(t)

def run_next_task():
    update_readyqueue()
    if len(readyqueue) == 0:
        return False
    t = readyqueue.pop()
    t.start()
    return True

def print_queues():
    global readyqueue
    global firsttaskqueue
    global nexttaskqueue
    global runninglist
    print ''
    print 'queue state'
    print 'readyqueue len', len(readyqueue), readyqueue
    print 'firsttaskqueue len', len(firsttaskqueue), firsttaskqueue
    print 'nexttaskqueue len',len(nexttaskqueue), nexttaskqueue
    print 'runninglist len', len(runninglist)
    print '\t', runninglist
    print 'insts_solved len', len(insts_solved)
    print '\t', insts_solved


def schedule():
    global insts_solved
    global num_cpus_used
    global firsttaskqueue
    global nexttaskqueue
    global runninglist
    global instances
    for i in range(len(str_instances)):
        l = InstState(i)
        instances += [l]
        for t in l.add_task():
            firsttaskqueue.push(t)

    # 启动时的调度
    update_readyqueue()
    if verb > 2:
        print_queues()

    while num_cpus_used < numCores:
        if run_next_task() is False:
            break

    # 执行时的调度
    while True:
        pid, retval=os.wait()       # 等待子进程结束
        num_cpus_used -= 1
        print 'pid %d over' % pid
        if pid in runninglist:
            task = runninglist[pid]
            task.taskstate = 'stop'
            del runninglist[pid]
            ins = task.inststate
            ins.cnt_runs_cur_state += 1
            print ''
            print 'c done inst%d' % ins.inst_id
            print '\t', task
            print '\t', ins

            res = task.get_result()

            if res == 'sat' or res == 'unsat':
                ins.result = res
                insts_solved += [ins]
            else:
                print 'time_out'
                ins.result = 'time_out'
                insts_solved += [ins]

        print 'solverd num:', len(insts_solved), '/', len(solverlist)*len(instances)
        if len(insts_solved) == len(solverlist) * len(instances):
            break

        # 选择新的任务执行
        if verb > 2:
            print 'readyqueue', readyqueue
            print ''
        while num_cpus_used < numCores:
            if run_next_task() is False:
                break

        if verb > 2:
            print_queues()

def add_solver(name, cmd, time_limit_str=None):
    global solverlist
    print solverlist
    s = Solver(name, cmd, len(solverlist))
    if time_limit_str != None:
        s.time_limit_str = time_limit_str
    solverlist += [s]

if __name__ == '__main__':
    if( len(sys.argv) < 2 ):
            print "c usage: sat_throughput.py <numCores> [<tmpDirectory>]"
            sys.exit(0)
    print "c running with PID " + str( os.getpid() )

    #
    # Handle parameters
    numCores=int(sys.argv[1])

    # setup tmp files
    tmpDir="/tmp/"
    print "c found " + str(len(sys.argv)) + " parameters"
    if(len(sys.argv)>4):
            tmpDir = sys.argv[4]
    if( tmpDir[-1:] != '/' ):
            tmpDir = tmpDir + "/"

    MAX_READY_NUM = numCores * 2
    all_start = time.time()
    py_start = clock()

    add_solver('minisat',      '/mirror/sat/workspace/minisat/binary/minisat_static -verb=1')
    # add_solver('minisat_blbd', '/mirror/sat/workspace/minisat_blbd/binary/minisat_blbd -verb=1')
    # add_solver('riss',         '/mirror/sat/workspace/riss/binary/rissDRAT')
    # add_solver('glucose',      '/mirror/sat/workspace/sgseq/glucose')
    # add_solver('zenn',         '/mirror/sat/workspace/zenn/binary/zenn')
    # add_solver('minisat_blbd', '/mirror/sat/workspace/minisat_blbd/binary/minisat_blbd -phase-saving=0')
    # add_solver('riss',         '/mirror/sat/workspace/riss/binary/rissDRAT -rer -ics')
    # add_solver('glucose',      '/mirror/sat/workspace/sgseq/glucose -phase-saving=0')
    # add_solver('riss',         '/mirror/sat/workspace/riss/binary/rissDRAT -phase-saving=0')
    # add_solver('riss',         '/mirror/sat/workspace/riss/binary/rissDRAT -fm -shuffle')
    # add_solver('riss',         '/mirror/sat/workspace/riss/binary/rissDRAT -inprocess -ee_sub')
    # add_solver('glucose',      '/mirror/sat/workspace/sgseq/glucose -K=0.7 -szLBDQueue=25')
    # add_solver('minisat',      '/mirror/sat/workspace/minisat/binary/minisat_static -phase-saving=0 -verb=1')

    # add_solver('ebglucose',    '/mirror/sat/workspace/satzilla/bin/ebglucose.sh')
    # add_solver('picosat',      '/mirror/sat/workspace/satzilla/bin/picosat-static')
    # add_solver('sattime',      '/mirror/sat/workspace/sgseq/sattime')
    # add_solver('forl',         '/mirror/sat/workspace/forl/binary/forl-nodrup', "--agillim ")
    # add_solver('nigma',        '/mirror/sat/workspace/nigma/binary/nigma')

    schedule()

    for ins in instances:
        print ""
        for t in ins.tasks:
            print "%-20s %-10s solver %-4d cpu time %f" % (t, t.solver.result, t.solver_id, t.solver.cputime)
    # # kill the other process, and its child processes
    # for p in pids:
    #  	os.kill(-p, 15)
            
    # print pidsseed
    # for i in pidsseed: 
    #     num = pidsseed[i]
    #     tmpFile=tmpDir + "sat_"+str(num)
    #     os.unlink(tmpFile + ".err")
    #     os.unlink(tmpFile + ".out")
    # 
    # exit with the correct exit code
    all_finish = time.time()
    py_finish = clock()
    print 'python runtime: %lfs' % (py_finish - py_start)
    print 'total runtime: %lfs' % (all_finish - all_start)

    sys.exit(0)
