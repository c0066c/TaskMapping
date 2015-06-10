INF = 100000000000000000

def hungarian(matrix):
    h, w,  = len(matrix), len(matrix[0]) 
    u, v, ind = [0]*h, [0]*w, [-1]*w
    for i in range(h):
        links, mins, visited = [-1]*w, [INF]*w, [False]*w
        markedI, markedJ, j = i, -1, 0
        while True:
            j = -1
            for j1 in range(h):
                if not visited[j1]:
                    cur = matrix[markedI][j1] - u[markedI] - v[j1]
                    if cur < mins[j1]:
                        mins[j1] = cur
                        links[j1] = markedJ
                    if j == -1 or mins[j1] < mins[j]: j = j1
            delta = mins[j]
            for j1 in range(w):
                if visited[j1]:
                    u[ind[j1]] += delta;  v[j1] -= delta
                else:
                    mins[j1] -= delta
            u[i] += delta
            visited[j] = True
            markedJ, markedI = j, ind[j] 
            if markedI == -1:
                break
        while True:
            if links[j] != -1:
                ind[j] = ind[links[j]]
                j = links[j]
            else:
                break
        ind[j] = i
    return [(ind[j], j) for j in range(w)]
'''
m = [[INF, 7858, 8743, 17325, 18510, 9231, 4920, 7056, 9701, 5034, 7825], 
     [8128, INF, 5021, 13603, 19635, 11386, 7075, 8840, 1843, 7189, 9256], 
     [6809, 5364, INF, 8582, 14614, 10067, 5756, 5904, 7207, 3882, 4235], 
     [7849, 5515, 1040, INF, 15654, 11107, 6796, 4713, 7358, 4900, 5275], 
     [10918, 8365, 4109, 5808, INF, 14176, 9865, 7928, 931, 7991, 8344], 
     [336, 7285, 2830, 11412, 17444, INF, 4347, 6483, 6688, 4461, 7065], 
     [1053, 2938, 3823, 12405, 15835, 4311, INF, 2136, 4781, 114, 2905], 
     [8930, 802, 5823, 14405, 20437, 12188, 7877, INF, 2645, 7429, 10058], 
     [9987, 7434, 3178, 11760, 17792, 13245, 8934, 6997, INF, 7060, 7413], 
     [10518, 2824, 3709, 12291, 15721, 13776, 9465, 2022, 4667, INF, 7944], 
     [2574, 4459, 5344, 9561, 17356, 5832, 1521, 3657, 6302, 1635, INF]
    ]
'''

#m = [[-10, -19 ,-8, -15,-19],[-10, -18, -7, -17,-19],[-13,-16,-9,-14,-19],[-12,-19,-8,-18,-19],[-14,-17,-10,-19,-19]]
m = [[10,5,4], [9,4,2],[8,3,1]]
print(hungarian(m))
