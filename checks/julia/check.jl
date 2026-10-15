# Independent check of the main theorem on small odd antiholes, by generic list colouring.
#
# The odd antihole on n = 2l - 1 vertices is the graph on 0, ..., n - 1 in which u and v are
# adjacent when they are distinct and not consecutive on the cycle. A list colouring is searched
# for vertex by vertex, checking every edge. For l = 3 every assignment of lists of size 2, and
# for l = 4 every assignment of lists of size 3 from at most 6 colours, up to renaming the
# colours, is checked: the antihole is colourable exactly when the lists are not all equal.
# For l = 5 and l = 6 random assignments are checked in the same way.
using Random

function antihole(n)
    [u != v && mod(u - v, n) != 1 && mod(v - u, n) != 1 for u in 0:n-1, v in 0:n-1]
end

function colourable(adj::Matrix{Bool}, lists::Vector{UInt32})
    n = length(lists)
    colour = zeros(Int, n)
    function go(v)
        v > n && return true
        m = lists[v]
        while m != 0
            c = trailing_zeros(m) + 1
            m &= m - one(UInt32)
            good = true
            for u in 1:v-1
                if adj[v, u] && colour[u] == c
                    good = false
                    break
                end
            end
            if good
                colour[v] = c
                go(v + 1) && return true
            end
        end
        colour[v] = 0
        return false
    end
    go(1)
end

allequal_lists(lists) = all(==(lists[1]), lists)

function enumerate_all(n, k, maxcol, adj)
    lists = zeros(UInt32, n)
    count = 0; constant = 0; failures = 0
    function rec(v, used)
        if v > n
            count += 1
            eq = allequal_lists(lists)
            constant += eq
            if colourable(adj, lists) == eq
                failures += 1
                failures <= 5 && println("  counterexample: ", string.(lists, base = 16))
            end
            return
        end
        for fresh in 0:k
            old = k - fresh
            (used + fresh > maxcol || old > used) && continue
            added = UInt32((1 << fresh) - 1) << used
            for s in UInt32(0):UInt32((1 << used) - 1)
                count_ones(s) == old || continue
                lists[v] = s | added
                rec(v + 1, used + fresh)
            end
        end
    end
    rec(1, 0)
    return count, constant, failures
end

function main()
    ok = true
    for (l, maxcol) in ((3, 10), (4, 6))
        n, k = 2l - 1, l - 1
        count, constant, failures = enumerate_all(n, k, maxcol, antihole(n))
        println("l = $l: $count assignments with at most $maxcol colours, $constant constant, ",
                "$failures failures")
        ok &= failures == 0 && constant == 1
    end
    rng = MersenneTwister(15102026)
    for l in 5:6
        n, k = 2l - 1, l - 1
        adj = antihole(n)
        c1 = colourable(adj, fill(UInt32((1 << k) - 1), n))
        c2 = colourable(adj, fill(UInt32((1 << l) - 1), n))
        failures = 0
        trials = 20000
        for t in 1:trials
            pal = k + 1 + rand(rng, 0:k+1)
            lists = zeros(UInt32, n)
            if iseven(t)
                while true
                    fill!(lists, UInt32((1 << k) - 1))
                    for _ in 1:rand(rng, 1:3)
                        v = rand(rng, 1:n); cin = rand(rng, 0:pal-1)
                        (lists[v] >> cin) & 1 == 1 && continue
                        bits = [b for b in 0:31 if (lists[v] >> b) & 1 == 1]
                        lists[v] = (lists[v] & ~(UInt32(1) << rand(rng, bits))) | (UInt32(1) << cin)
                    end
                    allequal_lists(lists) || break
                end
            else
                for v in 1:n
                    m = UInt32(0)
                    while count_ones(m) < k
                        m |= UInt32(1) << rand(rng, 0:pal-1)
                    end
                    lists[v] = m
                end
            end
            colourable(adj, lists) == allequal_lists(lists) && (failures += 1)
        end
        println("l = $l: constant lists of size $k ", c1 ? "colourable" : "not colourable",
                ", of size $l ", c2 ? "colourable" : "not colourable",
                "; $trials random assignments, $failures failures")
        ok &= failures == 0 && !c1 && c2
    end
    println(ok ? "Julia check passed" : "Julia check FAILED")
    exit(ok ? 0 : 1)
end

main()
