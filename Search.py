import copy
import heapq
import time

class Graph : # graph class
    hrad_nodes_time = []
    def __init__(self, E = [], V = 0, cur_node = 0, hards = {}, morids = {}) :
        self.E = E
        self.V = V
        self.cur_node = cur_node
        self.hards = hards
        self.morids = morids
    
    def __eq__(self, other) :
        return (self.E, self.V, self.cur_node, self.hards, self.morids) == \
               (other.E, other.V, other.cur_node, other.hards, other.morids)

    def add_edge(self, u, v):
        self.E[u-1].append(v-1)
        self.E[v-1].append(u-1)

    def set_morids(self):
        s = int(input())
        dis = {}
        for i in range(s):
            line = list(map(int, input().split()))
            dis[line[0]-1] = list(map(lambda x : x-1 , line[2:]))
            for j in range(len(dis[line[0]-1])):
                dis[line[0]-1][j] = [dis[line[0]-1][j], False]
        self.morids = dis

    def set_hards_v(self):
        int(input())
        h = list(map(int, input().split())) ;
        h = list(map(lambda x:x-1, h))
        self.hards = h
        self.hrad_nodes_time = [0 for _ in range(self.V)]

    def get_graph(self):
        n, m = map(int, input().split())
        self.E = [ [] for _ in range(n) ]
        for _ in range(m) :
            u, v = map(int, input().split())
            self.add_edge(u, v)
        self.V = n
        self.set_hards_v()
        self.set_morids()
        self.cur_node = int(input()) - 1
        
    def print_graph(self):
        print("*** GRAPH ***")
        for i in range(len(self.E)) :
            print(f" NODE {i+1} : {list(map(lambda x:x+1, self.E[i]))}")
        
        print("\n*** MORIDs ***")
        for m in self.morids.keys() :
            print(f"MORID {m+1} :", end=" ")
            for r in self.morids[m] :
                print(f"( {r[0]+1}, {r[1]} )", end="  ")
            print()

        print("\n*** HARD NODEs ***")
        for s in self.hards.keys() :
            print(f"node {s+1} : {self.hards[s]}")

    def increase_time_hard(self, hard_v) :
        self.hrad_nodes_time[hard_v] += 1

    def is_morid_ready(self, morid) :
        for r in self.morids[morid] :
            if r[1] == False :
                return False
        return True

    def set_cur_node(self, v) :
        self.cur_node = v

    def get_rec(self, cur) :
        for m in self.morids.keys() :
            for r in self.morids[m] :
                if r[0] == cur :
                    r[1] = True


class State :
    def __init__(self, graph, ready_m = set(), path = [], wait_for_think = 0, steps = 0) :
        self.graph = graph
        self.ready_m = ready_m
        self.path = path
        self.steps = steps
        self.wait_for_think = wait_for_think

    def __eq__(self, other):
        if other == None :
            return False
        return (self.wait_for_think, self.graph.cur_node, self.graph.morids, self.ready_m) ==\
               (other.wait_for_think, other.graph.cur_node, other.graph.morids, other.ready_m)
    
    def __lt__(self, other): 
        return self.steps < other.steps

    def create_state(self, v) :
        new_graph = copy.deepcopy(self.graph)
        new_graph.set_cur_node(v)
        new_graph.get_rec(cur = v)
        
        new_ready_m = copy.deepcopy(self.ready_m)
        if (v in new_graph.morids.keys()) and (new_graph.is_morid_ready(v)) :
            new_ready_m.add(v)

        new_path = copy.deepcopy(self.path)
        new_path.append(v+1)

        return State(graph = new_graph, ready_m = new_ready_m,\
                    path = new_path, wait_for_think=self.wait_for_think,\
                    steps = self.steps+1)

    def get_new_states(self) :
        new_states, v = [], self.graph.cur_node

        if v in self.graph.hards :
            if self.graph.hrad_nodes_time[v] > self.wait_for_think  :
                new_state = copy.deepcopy(self)
                new_state.steps += 1
                new_state.wait_for_think += 1
                return [new_state]

            self.wait_for_think = 0
            self.graph.increase_time_hard(v) 

        for n in self.graph.E[v] :
            new_states.append( self.create_state(n) )

        return new_states

    def is_goal(self) :
        v = self.graph.cur_node
        if len(self.ready_m) != len(self.graph.morids.keys()) :
            return False
        if v not in self.graph.morids.keys() :
            return False

        return True

    def find_length_between_rec(self) :
        start, end, length = self.graph.cur_node, [], 0
        qu, visited, parent = [], [], {}
        for m in self.graph.morids.keys() :
            for r in self.graph.morids[m] :
                if r[1] == False :
                    end.append(r[0])

        while len(qu) > 0 :

            cur_node = qu.pop(0)
            visited.append(cur_node)

            if cur_node in end :
                start, p = cur_node, cur_node
                end.remove(start)

                while p != start:
                    length += 1
                    p = parent[p]

                visited.clear()
                qu.clear(); qu.append(start)
                if len(end) == 0 :
                    break
                continue

            for n in self.graph.E[cur_node] :
                if (n not in visited) and (n not in qu):
                    qu.append(n)
                    parent[n] = cur_node

        return length

    def get_h(self) :
        result, not_ready_m = 0, []
        result += self.find_length_between_rec()

        for m in self.graph.morids.keys() :
            if m not in self.ready_m :
                not_ready_m.append(m)
                for r in self.graph.morids[m]:
                    if r[1] == False :
                        result += 1

        result += (self.graph.hrad_nodes_time[self.graph.cur_node] - self.wait_for_think)
        result += len(not_ready_m)

        return result


#####################  BFS  #######################

def BFS(init_state) :
    frontier, visited, visit_states = [], [], 0
    frontier.append(copy.deepcopy(init_state))

    while  len(frontier) > 0 :
        current_state = frontier.pop(0)
        visit_states += 1

        if current_state.is_goal() :
            path, cost_of_path = current_state.path, current_state.steps
            return path, cost_of_path, visit_states

        visited.append(current_state)            
        new_states = current_state.get_new_states()

        for s in new_states :
            if (s not in visited) and (s not in frontier)  :
                frontier.append(s)
    
    return None, None, visit_states



# ################## IDS ###################

def DFS(init_state, depth) :
    stack, visited, visit_states = [], [], 0
    stack.append(copy.deepcopy(init_state))

    while len(stack) > 0  :
        cur_state = stack.pop()

        if cur_state.is_goal() :
            return cur_state.path, cur_state.steps, visit_states, True
            
        if (cur_state.steps >= depth ) or ((cur_state, cur_state.steps) in visited):
            continue

        visit_states += 1
        visited.append((cur_state, cur_state.steps))

        new_states = cur_state.get_new_states()

        for s in new_states :
            if ( (s, s.steps) not in visited ) :
                stack.append(s)

    return None, None, visit_states, False

def IDS(init_state) :
    depth, total_visit_state = 1, 0
    while True :
        path, cost_of_path,visit_states, is_finish = DFS(copy.deepcopy(init_state), depth)
        total_visit_state += visit_states
        if is_finish :
            break
        depth += 1

        # print(f"Path : {path}\nCost Of Path : {cost_of_path}\nExecution Time : {end - start}\
        # \nSeen States in Depth {depth} : {visit_states}\
        # \nAll Seen States : {total_visit_state}\
        # \nDepth : {depth}")

    
    return path, cost_of_path, total_visit_state


#####################  A*  #######################

def Astar(init_state, alpha = 1) :
    frontier, front_list, visited, visited_state = [ [init_state.get_h()*alpha, init_state] ], [init_state], [], 0

    while len(frontier) > 0 :
        (h, cur_state) = heapq.heappop(frontier)

        if cur_state.is_goal() :
            return cur_state.path, cur_state.steps, visited_state

        visited.append(cur_state)
        visited_state += 1
        new_states = cur_state.get_new_states()

        for s in new_states :
            if (s not in visited) and (s not in front_list):
                heapq.heappush(frontier, [s.steps + s.get_h()*alpha, s] )
                front_list.append(s)

    return cur_state.path, cur_state.steps, visited_state




g = Graph()
g.get_graph()

initial_state = State(graph=g, path = [g.cur_node+1])

ExecutionTimeList = []
for i in range(3) :
    start = time.time()
    ###### CHOOSE ALGORITHM ######

    path, cost_of_path, visit_states = BFS(initial_state)
    # path, cost_of_path, visit_states = IDS(initial_state)
    # path, cost_of_path, visit_states = Astar(initial_state)
    # path, cost_of_path, visit_states = Astar(initial_state, alpha=1.6)
    # path, cost_of_path, visit_states = Astar(initial_state, alpha=7)

    end = time.time()
    ExecutionTimeList.append(end - start)

print(f"Path : {path}\nCost Of Path : {cost_of_path}\
        \nExecution Time : {sum(ExecutionTimeList)/3}\nSeen States : {visit_states}")

