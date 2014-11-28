'''This module solves LP using two-phase simplex method.
It is developed for teaching purpose only.

By Yingjie Lan (ylan@pku.edu.cn), Peking University
Date of latest update: 11/28/2014

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the
following conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY
OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT
LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
'''

'''
On windows use IDLE to open this file and run (F5);
Or simply double-click this file to run it.
On Apple you can run in a command prompt:
> python simplex.py

This works on Python2.6+, including Python 3.0+.
It might also work on older versions of Python.
'''


from fractions import Fraction as fract
import re #regular expression

import sys #for emulating Python 3 print
def puts(*args, **kwargs): #used in Python 2
    'emulating print function in Python 3'
    if 'file' in kwargs:
        redirect = sys.stdout
        sys.stdout = kwargs['file']
    else: redirect = None
    if 'sep' in kwargs: sep = kwargs['sep']
    else: sep = ' '
    what = sep.join(str(g) for g in args)
    try:
        if 'end' in kwargs:
            print ( '%s%s'%(what, kwargs['end']) ),
        else: print(what)
    finally:
        if redirect: sys.stdout = redirect

if 'raw_input' in dir(__builtins__):
    input = raw_input
else: #Python 3+
    puts = getattr(__builtins__, 'print')


puts('''
Welcome to simplex tableaux!
To abort ANYTIME, use "ctrl+C".
''')


class LPParser:
    '''
The grammar is case INsensitive.
1. comment start with a '#', till the end of line 
2. the first line must have the objective
3. the objective starts with either 'max' or 'min', 
   followed by a linear expression
4. a linear expression looks like: 3x + y + 12.5 z
5. next is a line with "ST" or equivalent 
6. a plain constraint may use '<', '>', '=', '>=', '<='
   to compare a linear expression with a constant 
7. a plain constraint may have a name, like "labor)".
8. variables are non-negative by default.
9. variables can be special kind: "free", "int", "bin"
10. model must end with a line with just "end".

max 6x + 4y #comment runs to the end of line
st #constraints starts here
    6x + 8y  <= 12
    10x+ 5y  <= 10
	free: y #y is free variable
end #end model.

Please see below for more examples.
'''
    def __init__(self, lines=()):
        self.sts = [] #constraints
        self.intvars = [] #integral variables
        self.fvs = None #free variables
        if type(lines) is str:
            lines = lines.split('\n')
        for line in lines:
            if self.parseLine(line): break
        else:
            if self.sts:
                puts("Warning: no END line.")
        self.vars = []
        for t,r,b,p in self.sts:
            for v in t:
                if v not in self.vars:
                    self.vars.append(v)
        self.vars = self.sortvars(self.vars)

    relsigns = {'>=':-1, '>':-1, '==':0, '=':0, '<=':1, '<':1}
    recogrels = re.compile('>=|<=|==|=|<|>')
    optsigns = {'MIN':-1, 'MAX':1}
    recogsign = re.compile('[+-]')

    sign2rel = [' == ', ' <= ', ' >= ']
    def __repr__(self):
        if not self.sts: return ''
        def maketerms(td):
            termvars = self.sortvars([v for v in td])
            terms = []
            for i, v in enumerate(termvars):
                c = td[v]
                if c == '1' or c == '-1': c = c[:-1]
                if i==0 or c.startswith('-'):
                    terms.append(' %s %s'%(c,v))
                else: terms.append(' +%s %s'%(c,v))
            return ''.join(terms)
        t,r,b,p = self.sts[0]
        obj = p + ('Max' if r>0 else 'Min') + maketerms(t)
        lines = [obj, 'Subject To']
        for i, (t,r,b,p) in enumerate(self.sts):
            if i==0: continue #ignore objective
            lines.append(p+maketerms(t)+ self.sign2rel[r]+ b)
        if self.fvs: lines.append("free: "+', '.join(self.fvs))
        if self.intvars: lines.append("int: "+', '.join(self.intvars))
        lines.append('End')
        return '\n'.join(lines)
    
    def parseLine(self, line):
        if line.startswith('##'):
            return puts(line[2:]) #full comment
        comment = line.find('#')
        if comment>=0: line = line[:comment]
        iconstr = line.find(')') #to name constraints
        if iconstr >=0:
            coname = line[:iconstr+1]
            line = line[iconstr+1:]
        else: coname = ''
        line = line.strip().upper()
        if not line: return #empty line
        if not self.sts:
            assert line[:4] in ('MAX ', 'MIN '),\
                "Hint: Objective must start with MAX/MIN!"
            self.sts.append((self.parseTerms(line[4:]),
                             self.optsigns[line[:3]], 0, coname))
        elif self.fvs is None:
            line=' '.join(line.split())
            assert line in ('ST', 'S.T.', 'SUBJECT TO', 'SUCH THAT'),\
                "Expect 'ST', 'S.T.', 'SUBJECT TO', or 'SUCH THAT'."
            self.fvs =  [] # free variables
        elif line == 'END': return True #done!
        elif line.startswith('FREE:'): #free variable declaration
            for name in line[5:].split(','):
                name = name.strip()
                assert self.recogvar.match(name), "Illigal var: "+name
                assert name not in self.intvars, "Both INT and FREE:"+name
                if name not in self.fvs: self.fvs.append(name)
        elif line.startswith('INT:'): #integral variables
            for name in line[4:].split(','):
                name = name.strip()
                assert self.recogvar.match(name), "Illigal var: "+name
                assert name not in self.fvs, "Both INT and FREE:"+name
                if name not in self.intvars: self.intvars.append(name)
        elif line.startswith('BIN:'): #binary variables
            for name in line[4:].split(','):
                name = name.strip()
                assert self.recogvar.match(name), "Illigal var: "+name
                assert name not in self.fvs, "Both BIN and FREE:"+name
                assert name not in self.intvars, "Already integral: "+name
                self.intvars.append(name)
                self.sts.append(({name:'1'}, self.relsigns['<'], 
						'1', '%s]'%name))
        else: #parse a constraint
            segs = [s.strip() for s in self.recogrels.split(line)]
            assert len(segs)==2, "Must have exactly one comparison!"
            assert self.recognum.match(segs[1]), 'illegal number: '+segs[1]
            rels = self.recogrels.search(line)
            rels = line[rels.start():rels.end()]     
            terms = self.parseTerms(segs[0])
            self.sts.append((terms, self.relsigns[rels], segs[1], coname))

    recogvar = re.compile('[a-zA-Z][a-zA-Z0-9]*$')
    recognum = re.compile('^[+-]?(?:(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*|[.][0-9]*)?|[.][0-9]+)$')
    
    def parseTerms(self, line):
        line = line.strip() #trip off starting and ending white spaces
        assert line, "there is no terms!"
        terms = [t.strip() for t in self.recogsign.split(line)]
        signs = self.recogsign.findall(line)
        assert terms[-1], "Must not end with a sign:\n"+line
        if terms[0]: signs.insert(0,'+')
        else: del terms[0]
        assert len(terms)==len(signs), "they must match."
        signedterms = {}
        for t,s in zip(terms, signs):
            mo = self.recogvar.search(t)
            assert mo, "Each term must contain a variable!\n"+line
            pos = mo.start()
            varname = t[pos:] #all upper case
            assert varname not in signedterms,\
                   "Repeated variable name!\n"+line
            coeff = t[:pos].strip() if pos else '1'
            assert self.recognum.match(coeff),\
                   "illegal number! "+coeff
            if s=='+': s = '' #don't need '+'
            signedterms[varname] = s+coeff
        return signedterms

    varindex = re.compile('[0-9]+$')
    leading0s = re.compile('^0+')

    def sortvars(self, varnames):
        varnames.sort(reverse=True)
        for i, v in enumerate(varnames):
            m = self.varindex.search(v)
            if m:
                idx = v[m.start():]
                v=v[int(v.startswith('!')):m.start()]
                m = self.leading0s.search(idx)
                if m: idx = idx[m.end():]
                idx = int(idx)
            else:
                idx = -1
                if v.startswith('!'): v = v[1:]
            varnames[i] = (varnames[i], v, idx)
        varnames.sort(key=lambda t: t[2])
        varnames.sort(key=lambda t: t[1])
        return [t[0] for t in varnames]

    def solver(self):
        if self.intvars:
            return BnBsolver(self)
        return Tableau(self)

from random import randint #wolf perturbation

def checkask(msg, default, values):
    while True:
        s = input(msg)
        if not s: return default
        if s not in values:
            puts("Bad choice. ", end='')
            continue
        return s

Infty = "Infty"

class Tableau(object):

    def __init__(self, prob, interactive=True):
        '''no variable name should start with '@' in prob.'''
        self.text = str(prob)
        self.vars = [''] #reserved
        def terms(td):
            ts = {}
            for v,c in td.items(): ts[v] = fract(c)
            return ts
        sts = [(terms(t),r, fract(b)) for t,r,b,p in prob.sts]
        self.rownames = [p for t,r,b,p in prob.sts]
        for i, (t,r,b) in enumerate(sts):
            if i==0: self.obj_dir = r
            if i==0 and r<0 or i and b < 0: #minimize or b<0
                for v in t: t[v] = -t[v]
                sts[i] = t, -r, -b
            for v in prob.fvs: #free vars
                if v not in t: continue
                t['!%s'%v] = - t[v] #negate coefficient
            for v in t:
                if v not in self.vars:
                    self.vars.append(v)
                    
        self.vars = prob.sortvars(self.vars) #sort by var name
        self.vars[0] = '(RHS)'
        
        #add surplus vars
        for idx, (t,r,b) in enumerate(sts):
            if r>=0: continue
            v = '#%i'%idx
            t[v] = -1
            self.vars.append(v)
        #add slack vars
        for idx, (t,r,b) in enumerate(sts):
            if idx==0 or r<=0: continue
            v = '$%i'%idx #slack
            t[v] = 1
            self.vars.append(v)
        #add artificial vars, in the end.
        #NOTE: not matrix I
        for idx, (t,r,b) in enumerate(sts):
            if idx==0 or r>0: continue
            v = '@%i'%idx #artificial
            t[v] = 1
            self.vars.append(v)
        #ready for tableau
        fobj = sts[0][0]
        self.fobj = [fobj.get(v,0) for v in self.vars]
        self.origrows = [None]
        for i, (t,r,b) in enumerate(sts):
            if i==0: continue #ignore objective
            row = [t.get(v,0) for v in self.vars]
            row[0] = b
            self.origrows.append(row)

        self._method = Tableau._largest_sigma
        self.interactive = interactive
        #The virtual perturbation is not proven
        self.virtual_perturbation = False
        #we may also use flat wolf randomization
        self.flat_wolf = not interactive
        #degenerated rows for wolf randomization
        self.degenerated = ()        
        self.hist = [] #history, to undo

    @property
    def meth(self):
        if self._method == Tableau._best_objective:
            return "best_objective"
        if self._method == Tableau._smallest_index:
            return "smallest_index"
        if self._method == Tableau._largest_sigma:
            return "largest_sigma"
        return "user_choice"

    @meth.setter
    def meth(self, name):
        if name == "best_objective":
            self._method = Tableau._best_objective
        elif name == "smallest_index":
            self._method = Tableau._smallest_index
        elif name == "largest_sigma":
            self._method = Tableau._largest_sigma
        elif name == 'user_choice':
            self._method = Tableau._user_choice            
        else: raise ValueError("unknown method: "+name)

    def _pivot_element(self):
        c = self._method(self)
        if type(c) is not int:
            return c #user choice
        r = self._pivot_row(c) if c else 0
        return r, c


    def _improvement(self, c):
        ratio = [ r[0]/r[c] for r in self.rows[1:] if r[c]>0]
        if len(ratio) == 0: return None #float('infinity')
        return min(ratio)*self.rows[0][c]

    def _best_objective(self):
        best, idx, sigma = fract(-1), 0, self.rows[0]
        for i in range(1, self.cols):
            if sigma[i] <= 0: continue
            imp = self._improvement(i)
            if imp is None: return i #infinity
            if imp <= best: continue #infty can't be converted
            best, idx = imp, i
        return idx #0: reached optimality
 
    def _smallest_index(self):
        sigma = self.rows[0]
        for i in range(1, self.cols):
            if sigma[i] > 0: return i
        return 0 #reached optimality

    def _largest_sigma(self):
        best, idx, sigma = fract(0), 0, self.rows[0]
        for i in range(1, self.cols):
            if sigma[i] <= best: continue
            best, idx = sigma[i], i
        return idx #0: reached optimality
 
    _auto_choice = _smallest_index
    def _user_choice(self):
       if not self.interactive:
           return self._auto_choice()
       ub =  self.cols - 1
       choices = [str(i) for i in range(ub+1)]
       c = int(checkask("Which column? 1-%i [auto]:"%ub, '0', choices))
       if c == 0:
           c = self._auto_choice()
           puts("Auto column: %i"%c)
       ub = len(self.rows) - 1
       choices = [str(i) for i in range(ub+1)]
       r = int(checkask("Which row? 1-%i [auto]:"%ub, '0', choices))
       if r == 0:
           r = self._pivot_row(c)
           puts("Auto row: %i"%r)
       return r, c

    def _restore(self):
        for  i in range(1,self.m+1):#self.degenerated:
            #restore the RHS: B^{-1} b
            self.rows[i][0] = sum(b*vi for b,vi in
                        zip(self.b, self.rows[i][-self.m:]))
        #restore the objective value too
        self.rows[0][0] = self.vobj
        self.degenerated = () #out of degeneracy
        if not self.interactive: return
        puts("Out of degeneracy! Restored tableau:")
        self.display()

    def _pivot_row(self, col):
        '''always use "smallest_index" to break tie.'''
        if self.degenerated:
            rows = self.degenerated
            puts("degenerated rows:"+ repr(rows))
        else: rows = list(range(1,self.m+1))
        rhs = [self.rows[i][0] for i in rows]
        lhs = [self.rows[i][col] for i in rows]
        ratio = [r/l for l,r in zip(lhs,rhs) if l>0]

        if len(ratio) == 0:
            if not self.degenerated: return 0 #infinite solution
            #OK, we found a way out of degeneracy!
            self._restore()
            return self._pivot_row(col)

        mrat = min(ratio) #ratio==0: degenerated!
        nrat = sum(1 for r in ratio if r==mrat)
        needcare = (mrat == 0 and nrat > 1)

        if needcare and self.virtual_perturbation: 
            lmin, idx = max(lhs)+1, 0
            for i, l, r in zip(rows, lhs, rhs):
                if r == 0 and (lmin > l > 0):
                    lmin, idx = l, i
            return idx #which has lmin, to break cycle
        
        if needcare and self.flat_wolf:
            if not self.degenerated:
                self.vobj = self.rows[0][0] #remember objective value
                self.degenerated = [i for i in rows if self.rows[i][0]==0]
            for i in self.degenerated:
                if self.rows[i][0]: continue #re-randomize?
                #wolf randomization, without recursion (flat)
                self.rows[i][0] = fract(1)/randint(2,10)
            return self._pivot_row(col)

        smallest, ri = len(self.vars) + 1, -1
        for i, l, r in zip(rows, lhs, rhs): #min ratio
            if l <= 0: continue
            if r == mrat * l: #fractions
                if self.base[i] < smallest:
                   smallest, ri = self.base[i], i #smallest_index
        assert ri >= 0, "row index should never be negative!"
        return ri #smallest_index

    def display(self, r=0, itn=None, sep="\t", asformula=False):
        if itn is None: itn = len(self.hist)
        varn, nvars = self.vars[:self.cols], self.cols
        puts(sep.join(varn[c-1] if c else '[%i]'%itn 
				for c in range(nvars+1)))
        base = [varn[b] if b else 'sigma' for b in self.base]
        if r: base[r] = base[r]+'*'
        for b, crow in zip(base, self.rows):
            if asformula:
                puts(sep.join('=%s'%crow[c-1] if c else b
				for c in range(nvars+1)))
            else:
                puts(sep.join(str(crow[c-1]) if c else b
				for c in range(nvars+1)))
        if not asformula:
            puts('column select: %s, per[t]urbation: %r, [w]olf: %r'
             %(self.meth, self.virtual_perturbation, self.flat_wolf))

 
    def _pivot(self, row, col, hist=True):
        e = self.rows[row][col]
        self.rows[row] =  [k/e for k in self.rows[row]]
        for r in range(len(self.rows)):
            if r == row: continue
            e = self.rows[r][col]
            if e==0: continue
            self.rows[r] = [d-e*s for d,s in
                    zip(self.rows[r],self.rows[row])]
        if hist: self.hist.append((self.base[row], col))
        self.base[row] = col #must go after history update

    def undo(self):
        if not self.hist: return 0
        vout, vin = self.hist.pop()
        r = self.base.index(vin)
        self._pivot(r, vout, False)
        return r
    
    def ipeek(self):
        current = last = len(self.hist) - 1
        while True:
            s = input("Peek menu: 1.prev 2.next 3.abort: ")
            if '1' in s:
                if current < 0:
                    puts("Already at beginning.")
                    continue
                vout, vin = self.hist[current]
                r = self.base.index(vin)
                self._pivot(r, vout, False)
                self.display(r, current)
                current -= 1
                continue
            if '2' in s:
                if current >= last:
                    puts("Already at last, choose 3 to abort.")
                    continue
                current += 1
                vout, vin = self.hist[current]
                r = self.base.index(vout)
                self._pivot(r, vin, False)
                self.display(r, current+1)
                continue
            if '3' in s:
                while current < last:
                    current += 1
                    vout, vin = self.hist[current]
                    r = self.base.index(vout)
                    self._pivot(r, vin, False)
                return r
            puts("Bad choice! ", end='')
            
    def shake(self):
        #ramble RHS by adding random numbers
        rhs = [self.rows[r][0] for r in range(self.m+1)]
        for r in range(1, self.m+1):
            self.rows[r][0] += randint(1, 20)
        current = last = len(self.hist) - 1
        while current >= 0:
            vout, vin = self.hist[current]
            r = self.base.index(vin)
            self._pivot(r, vout, False)
            current -= 1
            if min(self.rows[t][0] for t in range(1,self.m+1))<0:
                puts("SHAKER found infeasibility!")
                self.display(r, current+1)
                inf = True
                break
        else: inf = False
        while current < last:
            current += 1
            vout, vin = self.hist[current]
            r = self.base.index(vout)
            self._pivot(r, vin, False)
        if inf:
            puts([self.rows[rr][0] for rr in range(self.m+1)])
        for rr in range(1, self.m+1):
            self.rows[rr][0]  = rhs[rr]
        return r

    def ihelp(self):
        if self.interactive: puts("""
===================|| Interaction Help ||===================

After each tableau, you are given the rule of operation.
Then you are given four options of pivot method:
    1.sigma: choose entering column by largest sigma
    2.index: choose entering column by smallest index
    3.objective: choose entering column by best improvement
    4.user: input your own entering column and row

If you just hit the 'return' key, nothing will change.
To choose a method, type the digit. To toggle the perturbation
status, type 't'. To enable wolf randomization, type 'w'.
If you just need the final result, type 'go'.
You may combine a number, a 't', a 'w', and a 'go' together.
Type 'undo' to undo, type 'peek' to peek at previous tableaux.
""")

    method_names = ('largest_sigma', 'smallest_index', 'best_objective', 'user_choice')
    def interact(self, r=0):
        if not self.interactive: return
        self.display(r)
        s = input("1.sigma 2.index 3.objective 4.user: ").lower()
        if not s: return #no changes
        if 't' in s: #swap perturbation
            self.virtual_perturbation = not self.virtual_perturbation
            puts("virtual perturbation:", self.virtual_perturbation)
        if 'w' in s:
            self.flat_wolf = not self.flat_wolf 
            if self.flat_wolf: self.virtual_perturbation = False
            puts("flat wolf randomization:", self.flat_wolf)

        mc = [c for c in '1234' if c in s]
        if len(mc)>1:
            puts("Can't choose multiple methods at one time.")
        elif mc:
            self.meth = self.method_names[ord(mc[0])-ord('1')]
            #puts("method changed to: %s" % self._method)
        if 'go' in s:
            self.interactive = False
            puts("Turned off interaction.")
        if 'undo' == s:
            #while input("Undo? [y]/n") not in ('n','N'):
            r = self.undo()
            if r: self.display(r)
            else:
                puts("Already at the first tableau.")
                #break
            #ask about what to do next
            self.interact(r)
        elif 'peek' == s:
            r = self.ipeek()
            self.interact(r)
        elif 'shake' == s:
            r = self.shake()
            self.interact(r)


    def _phase_solve(self, maxit):
        puts("Start Phase %s."%[0,'I','II'][self.phase])
        self.interact()
        while maxit:
            r, c = self._pivot_element()
            if c == 0:
                puts("Found optimal solution at iteration [%i]!"
                      % len(self.hist))
                if self.degenerated: self._restore()
                self.hist.append((r, c))
                return self.phase
            if r == 0:
                puts("Infinite solutionn!")
                self.phase = 3
                self.hist.append((r, c))
                return 0
            self._pivot(r,c)
            self.interact(r)
            maxit -= 1
        puts("Hit max iteration!")
        self.phase = - self.phase #may continue
        return 0

    def _transfer_to_phase_II(self):
        if self.phase != 1: return False
        if self.rows[0][0] != 0:
            puts("Not feasible to start Phase II!")
            return False 
        puts('''\n***** Transition to phase II *****\n''')
        #make sure no artificial variable is in the base
        for r, b in enumerate(self.base[:]):
            if self.vars[b][0] != '@': continue #not artificial
            #degenerated(artificials in the base), swap them out
            for c, v in enumerate(self.rows[r]):
                #v<0 is OK! this is only true when degenerated.
                if c in self.base or v==0: continue
                #don't swap in an artificial one
                if self.vars[c][0] == '@': continue
                #swap in a non-base, non-artificial variable!
                self._pivot(r, c); break 
            else:
                self.display(r)
                raise Exception("Can't remove %s!"%self.vars[b])
        #delete artificial variables
        for i, v in enumerate(self.vars[-self.m:]):
            if v[0]!='@': continue
            self.cols -= 1
        #update the sigma
        sigma = self.fobj[:] #NOTE: may need update
        for r, b in enumerate(self.base):
            e = sigma[b]
            if r == 0 or e==0: continue
            sigma = [c-e*v for c,v in zip(sigma, self.rows[r])]
        self.rows[0] = sigma
        self.phase = 2
        self.hist_I = self.hist #save history
        self.hist = [] #clear history
        return True

    def _init_base(self):
        self.rows = self.origrows[:]
        for i, row in enumerate(self.rows):
            if not row: continue
            self.rows[i] = row[:]
        self.m = len(self.rows)-1 #excluding objective row
        self.b = [v[0] for v in self.rows if v] #initial b
        nvars = len(self.vars)
        self.base = list(range(nvars-self.m-1, nvars))
        self.base[0] = 0 #reserved for the objective row
        self.cols = nvars #0 for RHS
        for vi in range(nvars-self.m, nvars):
            if self.vars[vi][0]=='@': break
        else: #no artificial variables
            self.rows[0] = self.fobj[:]
            self.phase = 2 
            return
        #with artificial variables
        self.phase = 1
        sigma = [fract(-1) if self.vars[i][0]=='@' else fract(0)
                   for i, a in enumerate(self.fobj)]
        for b, row in zip(self.base, self.rows):
            if row is None: continue
            if self.vars[b][0]!='@': continue
            sigma = [c+v for c,v in zip(sigma,row)]
        self.rows[0] = sigma

    def solve(self, maxit=-1):
        self._init_base()
        self.ihelp()
        opt = self._phase_solve(maxit)

        if self._transfer_to_phase_II():
            opt = self._phase_solve(maxit)

        if opt==2: #optimality?
            return True

        self.savework()

    def _phase_follow(self, hist):
        puts("Start Phase %s."%[0,'I','II'][self.phase])
        self.display(itn=0, asformula=True)
        for itn, (vout, c) in enumerate(hist):
            r = self.base.index(vout)
            if c == 0:
                puts("Found optimal solution at iteration [%i]!"
                      % len(self.hist))
                if self.degenerated: self._restore()
                self.hist.append((r, c))
                return self.phase
            if r == 0:
                puts("Infinite solutionn!")
                self.phase = 3
                self.hist.append((r, c))
                return 0
            self._pivot(r,c)
            self.display(r, 1+itn, asformula=True)
        self.phase = - self.phase #may continue
        return 0

    def auto_replay(self): #to save to excel file
        self._init_base() #phase?

        hist = self.hist_I if self.phase==1 else self.hist
        saved_hist = self.hist
        self.hist = []

        opt = self._phase_follow(hist)
        if self._transfer_to_phase_II():
            opt = self._phase_follow(saved_hist)

        assert self.hist == saved_hist, "Inconsistency in history!"

        if opt!=2: return #optimality?
        if self.phase != 2:
            return puts("No optimal solution")
        #phase 2 optimality
        self.sensit()
        self.printSoln("%s\t=%s\t=%s")
        self.printCons("%s\t=%s\t=%s")
        self.printCoefRange("%s\t=%s\t=%s\t=%s")
        self.printConsRange("%s\t=%s\t=%s\t=%s")

    def savework(self):
        global Infty
        savef = input("Save to file (return to skip):").strip()
        if not savef: return
        savef = "%s.xls"%savef
        with open(savef, "wt") as saved:
            redirect = sys.stdout
            sys.stdout = saved
            Infty = "B1" #see below
            puts("NOTE:\tInfty\tdenotes infinity.") #in B1
            puts("HINT: You can format numbers as fractions in excel.")
            puts(self.text)
            self.auto_replay()
            puts()
            sys.stdout = redirect
            Infty = "Infty" #restore
        puts("saved to file: %s"%savef)

    def report(self):
        if self.phase != 2:
            puts("No optimal solution")
            return self.savework()

        #phase 2 optimality
        self.sensit()
        self.printSoln()
        self.printCons()
        if 'n' in input("Sensitivity Report?[y]/n"):
            pass
        else:
            self.printCoefRange()
            self.printConsRange()

        self.savework()

    def sensit(self): #sensitivity computations
        c = [self.fobj[i] for i in self.base if i]
        tiB = [self.rows[r][-self.m:] for r in range(1,self.m+1)]
        tiB = list(zip(*tiB)) #transposed
        self.shadow = [sum(ci*bi for ci, bi in zip(c, tiB[i]))
             for i in range(self.m)]
        if self.obj_dir<0: #assuming positive RHS
            self.shadow = [-s for s in self.shadow]
        #now we do range of RHS
        sig = [v[0] for i, v in enumerate(self.rows) if i]
        self.bu, self.bl = [], []
        for r in range(self.m):
            #sig + inc*tiB[r] >= 0
            vv = [sv/av for sv,av in zip(sig,tiB[r]) if av<0]
            u =  self.b[r] - max(vv) if vv else Infty
            vv = [sv/av for sv,av in zip(sig,tiB[r]) if av>0]
            l =  self.b[r] - min(vv) if vv else Infty
            self.bu.append(u)
            self.bl.append(l)
            

    def getObj(self): return - self.obj_dir * self.rows[0][0]
    def getSolution(self):
        def getX(i, v):
            if i==0: return '(Obj)', self.getObj()
            if i in self.base:
                return v,self.rows[self.base.index(i)][0]
            if i+1 < len(self.vars) and\
               self.vars[i+1][0]=='!' and i+1 in self.base:
                    return v,-self.rows[self.base.index(i)][0]
            return v, fract(0)
        return [getX(i,v) for i,v in enumerate(self.vars)
                if v[0] not in '#@$!']

    def printSoln(self, tpl = "%s\t\t%s\t\t%s"):
        puts("Optimal objective value: %s"%str(self.getObj()))
        puts("Optimal Solution:")
        puts("Variable\tActivity\tReduced Cost")
        #reduced cost: what if its nonnegative bound is reduced
        for i,v in enumerate(self.vars):
            if not i: continue
            if v[0] in '#@$': break
            if i in self.base:
                a = str(self.rows[self.base.index(i)][0])
                d = '0'
            else:
                a = '0'
                d = str(-self.rows[0][i])
            puts(tpl%(v, a, d))
        #mylist.sub( :x => x+2 )

    def getCoefRange(self, i):
        a = self.fobj[i]
        if i in self.base:
            sig = self.rows[0]
            row = self.rows[self.base.index(i)]
            #sig[c] - row[c]*inc <= 0
            ubs = [sig[c]/row[c] for c in range(1,self.cols) if row[c] < 0]
            u = a + min(ubs) if ubs else Infty
            #sig[c] + row[c]*dec <= 0
            ubs = [sig[c]/row[c] for c in range(1, self.cols)
                   if (c!=i and row[c] > 0)]
            l = a + max(ubs) if ubs else Infty 
        else:
            l = Infty
            u = a - self.rows[0][i]
        def neg(u): return u if type(u) is str else -u
        return (l, a, u) if self.obj_dir>0 else (neg(u),-a,neg(l))

    def printCoefRange(self, tpl="%s\t\t%s\t\t%s\t\t%s"):
        puts("Sensitivity on coefficients:")
        puts("Variable\tLower Bound\tCoefficient\tUpper Bound")
        for i,v in enumerate(self.vars):
            if not i: continue
            if v[0] in '#@$': break
            l, a, u = self.getCoefRange(i)
            puts(tpl%(v, l, a, u))

    def printCons(self, tpl="%s\t%s\t\t%s"): #constraints
        puts("Constraint Activities:")
        puts("ID\tSlack/Surplus\tShadow Price")
        for i in range(1,self.m+1):
            vi = 0
            if '#%i'%i in self.vars: #surplus
                vi = self.vars.index('#%i'%i)
            elif '$%i'%i in self.vars: #slack
                vi = self.vars.index('$%i'%i)
            if vi and vi in self.base:
                v = self.rows[self.base.index(vi)][0]
            else: v = 0 #nonbasic or artificial
            rname = self.rownames[i]
            puts(tpl%(rname if rname else i,
                                 v,self.shadow[i-1]))

    def printConsRange(self, tpl="%s\t%s\t\t%s\t\t%s"): #constraints
        puts("Sensitivity on R.H.S.:")
        puts("ID\tLower Bound\tCurrent Value\tUpper Bound")
        for i in range(self.m):
            rname = self.rownames[i+1]
            puts(tpl%(rname if rname else i+1,
                self.bl[i], self.b[i], self.bu[i]))

class Node:
    offinc = "   "
    verbose = False
    def __init__(self, noid, prob, note, parent=None):
        self.parent = parent
        self.noid = noid
        self.note = note
        for b in reversed(self.bounds()):
            prob.parseLine(b)
        puts(repr(prob))
        tab = Tableau(prob, self.verbose)
        if tab.solve(): soln=tab.getSolution()
        else: soln = None
        self.soln = soln
        self.left = self.right = None

    def bounds(self):
        bounds = []
        while self.parent:
            bounds.append(self.note)
            self = self.parent
        return bounds

    def pprint(self, offset):
        if self.soln:
            soln = [v+':'+str(f) for v, f in self.soln]
        else: soln = ("Infeasible",)
        puts(offset+("[%i]"%self.noid)
              +self.note+": "+','.join(soln))
        if not self.left: return
        offset += self.offinc
        self.left.pprint(offset)
        self.right.pprint(offset)

class BnBsolver:
    '''branch and bound solver for IP.
It prints out current BnB tree and asks for user input.'''

    def __init__(self, prob):
        self.root = Node(0, prob, "root")
        self.nodes = [self.root]
        self.prob = prob #the problem
        self.morig = len(prob.sts) - 1 #original m
        if self.root.soln:
            self.vars = [v for v,s in self.root.soln]
        else: self.vars = None
        self.intvars = prob.intvars


    def chooseNode(self):
        for i, node in enumerate(self.nodes):
            if node.left: continue
            if node.soln is None: continue
            for v, s in node.soln[1:]:
                if s != int(s): break
            else: continue
            return i
        return None

    def askNode(self):
        ser  = len(self.nodes)
        choices = [str(i) for i in range(ser)]
        while True:
            c = int(checkask(
                "Choose node, 0-%i [auto]:"%(ser-1), '-1', choices))
            if c>=0:
                node = self.nodes[c]
                if node.left or node.soln is None:
                    puts("Bad choice! ", end='')
                    continue
            else: #auto
                c  = self.chooseNode()
                puts("Chosen [%s]."%c)
            return c

    def chooseVar(self, c):
        node = self.nodes[c]
        for v in self.intvars:
            vi = self.vars.index(v)
            val  = node.soln[vi][1]
            if val.denominator == 1: continue
            return vi
        return None #already integer soln!
    
    def askVar(self, c):
        node = self.nodes[c]
        while True:
            puts(self.intvars)
            v = checkask("Choose variable [auto]:", '', self.intvars)
            if v:
                vi = self.vars.index(v)
                val = node.soln[vi][1]
                if val.denominator == 1:
                    puts("Bad choice! ", end='')
                    continue
            else:
                vi  = self.chooseVar(c)
                if vi: puts("Chosen '%s'. "%self.vars[vi])
            return vi
            
    def interact(self):
        puts("Current B&B tree:")
        self.root.pprint("")
        c = self.askNode()
        if c is None: return c,c
        v = self.askVar(c)
        return c, v

    def drill(self, c, v):
        'drill down node c, with variable v'
        node = self.nodes[c]
        assert not node.left and node.soln, "Bad node!"
        s = node.soln[v][1]
        assert s.denominator!=1, "Bad variable!"
        vname, prob, left = self.vars[v], self.prob, int(s)
        note = "%s <= %i"%(vname, left)
        del self.prob.sts[self.morig+1:] # remove non-original
        node.left = Node(len(self.nodes), prob, note, node)
        self.nodes.append(node.left)
        note = "%s >= %i"%(vname, left+1)
        del self.prob.sts[self.morig+1:] # remove non-original
        node.right = Node(len(self.nodes), prob, note, node)
        self.nodes.append(node.right)

    def solve(self):
        while input("Continue? [y]/n") in 'yY':
            c, v = self.interact()
            if c is None:
                puts("All nodes explored!")
                break
            if v is None:
                #self.foundIntSoln(c)
                continue
            self.drill(c,v)

exlp=("""
    max 6x + 4y + Z2 + Z1
    st
    6x + 8y  <= 12
    10x+ 5y  <= 10
    free: Z1, Z2 #test a free variable
    end #this ends the model
    """,
      """
MIN 3X1 +5/2X2 +7/2X3 -4X4 +1X5
SUCH THAT
   -1X1   +3X2   +5X3        +1X5 = 12
           +1X2   +3X3  +2X4  +3X5 = 10
    2X1   -1X2               +4X5 = 20
END""",
     """
MIN 10/7X1 +7/2X2          -4X4 +1X5
SUBJECT    To
             +2X2     -1X3    +3X4  +2X5 =   10
      2X1                    -4X4  +3X5 =   12
             -1X2     +1X3          +1X5 =   15
END
""",
      """
MIN X1 +3/2X2 +2X3 -3/2X4
S.T.
    4X1            -1X3  +3X4 =     8
    2X1      -3X2        -4X4 =    21
              -1X2  +3X3       =    15
end""",
"""
MIN 3X1 +7/2X2       -4X4 + X5
ST
            +3X2  -2X3    +3X4   +3X5 =  10
    2X1                  -4X4   +5X5 =  20
            -X2                 +X5 =  15
end""",
"""
##
## This cycling example is from Beale
## 
    max 3/4X1 -150X2 +1/50X3 -6X4
    st
        1/4X1 -60X2 -1/25X3 + 9X4 < 0
        1/2X1 -90X2 -1/50X3 + 3X4 < 0
                        # X3       < 1
    end""",
"""
##
## This cycling example is from Marshal and Suurballe
## 

MIN  -.4 X1 - .4 X2 + 1.8 X3
ST
1) .6 x1 - 6.4 x2 + 4.8 x3 < 0
2) .2 x1 - 1.8 x2 +  .6 x3 < 0
3) .4 x1 - 1.6 x2 +  .2 x3 < 0
#4)            x2          < 1
END""",
"""
max 100 x1 + 150 x2
st
8000 x1 + 4000x2 <= 40000
15 x1 + 30 x2 <= 200
int: x1, x2
end
""",
"""
max 10 x1 + 15 x2
st
8 x1 + 4x2 <= 40
15 x1 + 30 x2 <= 200
x2 <= 5
x2 <= 5
x2 <= 5
x2 <= 5
end
""")

def main():
    global solver
    while True:
        s = input("""
              ***  Menu  ***
        ============================
        0  The first linear program
        1  One optimal solution
        2  Multiple optimal solution
        3  Infeasible problem
        4  Infinite solution
        5  Cycling example (Beale)
        6  Marshal and Suurballe
        7  Branch and Bound example
        8  Define a linear program

Your choise (hit 'return' to quit) [0-8]:""")
        if len(s)==1 and s in '01234567':
            mod = exlp[ord(s)-ord('0')]
            p = LPParser(mod)
            puts("The parsed model is:\n%r"%p)
            input("""Hint: You may save as excel file later.
Hit 'enter/return' to continue...""")
            solver = p.solver()
            if solver.solve(): solver.report()
            continue
        if s!='8': break
        s = input('''
                        Input Format
  ==========================================================

  Comments start with '#' and continue to the end of line.
  Integers, decimals and fractions are acceptable numbers.
  Everything in the input is case INsensitive. 

  The first non-comment line must be the objective(min/max):
     min 5x + 0.1 y - z    # this is the objective
  The next line must be one of 'st', 's.t.', 'subject to', 
  and 'such that', indicating the start of constraints.
  Then each line afterwards gives a plain constraint like:
     3 x + 4 y + 1/2 z < 100 #use '=', '<', '>', '<=', '>='.
  A plain constraint can optionally have a name:
     labor) 3 x + 4 y + z < 100 #label will appear in report
  A special constraint begins with 'free:', 'int:', or 'bin:',
  followed by a list of variables of the indicated kind:
     free: x, y #x, y are free. int: integral, bin: binary
  A variable is non-negative and continuous by default.
  The last line should be "end" to indicate the end of model.

File name [to type in a model here, hit return]:''')
        if s:
            try:
                p = LPParser(open(s, 'rt'))
                puts("The parsed model is:\n%r"%p)
                input("hit 'return' to continue...")
                solver = p.solver()
                if solver.solve(): solver.report()
            except Exception as ex:
                puts(ex)
            continue
        puts("Type your model, end with a line of just 'END'.")
        p = LPParser()
        while True:
            s = input()
            lines = s.split('\n')
            try:
                for line in lines:
                    if p.parseLine(line):
                        break
                else:
                    continue
                break
            except Exception as ex:
                puts(ex)
        puts("The parsed model is:\n%r"%p)
        input("hit 'return' to continue...")        
        solver = p.solver()
        if solver.solve(): solver.report()


def debug(): #debug _pivot_row
    lp = """
max 10 x1 + 15 x2
st
8 x1 + 4x2 <= 40
15 x1 + 30 x2 <= 200
X2 >= 6
X2 >= 6
X2 >= 6
X2 >= 6
end
"""
    p = LPParser(lp)
    puts("The parsed model is:\n%r"%p)
    input("hit 'return' to continue...")
    global solver
    solver = p.solver()
    if solver.solve():
        solver.report()

if __name__ == '__main__':
    #debug()
    main()
