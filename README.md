# SatisfiabilitateMpi
#!/usr/bin/env python3

from collections import Counter, defaultdict
import sys, itertools

Literal = int
Clause  = set[int]
CNF     = list[Clause]

def _parse_clause(line: str, varmap: dict[str,int], next_id: list[int]) -> Clause:
    clause: Clause = set()
    for tok in line.replace('v', ' ').split():
        neg = tok.startswith(('~', '!'))
        if neg:
            tok = tok[1:]
        if not tok:
            continue
        if tok not in varmap:
            varmap[tok] = next_id[0]
            next_id[0] += 1
        lit = varmap[tok]
        clause.add(-lit if neg else lit)
    if not clause:
        raise ValueError('Clauză goală.')
    return clause


def cinput() -> tuple[CNF, dict[str,int]]:
    n = int(input('Numărul de clauze: ').strip())
    varmap: dict[str,int] = {}
    next_id = [1]
    cnf: CNF = [_parse_clause(input(f'Clauza {i+1}: '), varmap, next_id) for i in range(n)]
    return cnf, varmap


def _inv_map(m: dict[str,int]):
    return {v:k for k,v in m.items()}


def nice_assign(assign: dict[int,bool], inv: dict[int,str]):
    return ', '.join(f"{inv[v]}={'A' if b else 'F'}" for v,b in sorted(assign.items()))

def dp(cnf: CNF) -> bool:
    cnf = [c.copy() for c in cnf]
    while cnf:
        var = abs(next(iter(cnf[0])))
        pos = [c for c in cnf if  var in c]
        neg = [c for c in cnf if -var in c]
        resolvents: list[Clause] = []
        for c1 in pos:
            for c2 in neg:
                res = (c1 - { var}) | (c2 - {-var})
                if any(l in res and -l in res for l in res):
                    continue
                if not res:
                    return False
                resolvents.append(res)
        cnf = [c for c in cnf if var not in c and -var not in c]
        cnf.extend(resolvents)
    return True

def _unit_propagate(cnf: CNF, assign: dict[int,bool]):
    changed = True
    while changed:
        changed = False
        for c in cnf:
            unassigned = [l for l in c if abs(l) not in assign]
            if len(unassigned)==0 and not any((l>0)==assign.get(abs(l),False) for l in c):
                return False, cnf
            if len(unassigned)==1:
                lit = unassigned[0]
                assign[abs(lit)] = lit>0
                newcnf: CNF = []
                for d in cnf:
                    if lit in d:
                        continue
                    nd = {l for l in d if l != -lit}
                    newcnf.append(nd)
                cnf = newcnf
                changed = True
                break
    return True, cnf


def _pick_var_moms(cnf: CNF, assign: dict[int,bool]):
    length2 = [c for c in cnf if len(c)==2]
    counts = Counter(abs(l) for c in length2 for l in c if abs(l) not in assign)
    if counts:
        return counts.most_common(1)[0][0]
    counts = Counter(abs(l) for c in cnf for l in c if abs(l) not in assign)
    return counts.most_common(1)[0][0]


def _dpll(cnf: CNF, assign: dict[int,bool]) -> bool:
    ok, cnf = _unit_propagate(cnf, assign)
    if not ok:
        return False
    if not cnf:
        return True
    var = _pick_var_moms(cnf, assign)
    for val in (True, False):
        assign_local = assign.copy()
        assign_local[var] = val
        newcnf = []
        conflict = False
        for c in cnf:
            if (val and var in c) or (not val and -var in c):
                continue
            nc = {l for l in c if l not in (var if val else -var, -(var) if val else var)}
            if not nc:
                conflict = True
                break
            newcnf.append(nc)
        if not conflict and _dpll(newcnf, assign_local):
            assign.clear(); assign.update(assign_local)
            return True
    return False


def dpll(cnf: CNF):
    assign: dict[int,bool] = {}
    sat = _dpll([c.copy() for c in cnf], assign)
    return sat, assign

def refutation(cnf: CNF) -> bool:
    new = set()
    clauses = [frozenset(c) for c in cnf]
    while True:
        for c1, c2 in itertools.combinations(clauses, 2):
            for lit in c1:
                if -lit in c2:
                    res = frozenset(c1.union(c2) - {lit, -lit})
                    if not res:
                        return False
                    new.add(res)
        if new.issubset(set(clauses)):
            return True
        clauses.extend(new)

def banner():
    print('Rezolvator SAT Avansat')

def main():
    banner()
    while True:
        print('\nMetodă:\n 1) Davis–Putnam\n 2) DPLL (MOMS)\n 3) Rezoluție\n 4) Ieșire')
        ch = input('Selectează: ').strip()
        if ch=='4':
            print('La revedere!'); return
        cnf, vmap = cinput()
        if ch=='1':
            sat = dp(cnf); assign={}
        elif ch=='2':
            sat, assign = dpll(cnf)
        elif ch=='3':
            sat = refutation(cnf); assign={}
        else:
            print('Opțiune invalidă.'); continue
        inv = _inv_map(vmap)
        if sat:
            print('SATISFIABIL')
            if assign:
                print('Atribuire:', nice_assign(assign, inv))
        else:
            print('NESATISFIABIL')

if __name__=='__main__':
    try:
        main()
    except KeyboardInterrupt:
        print('\nOprit.', file=sys.stderr)
        sys.exit(1)
