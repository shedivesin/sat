// This SAT solver is an implementation of Knuth's Algorithm B (TAOCP 7.2.2.2).
// It's not the smallest SAT solver possible, but it is quite efficient for
// what it is, and ought to be capable of the toy problems I'm playing with!
function solve(formula) {
  // Validate the input and determine how many clauses, variables, and literals
  // we'll have, so we can allocate our data structures. Input is expected to
  // be an array of arrays of integers.
  let m = 0;
  let n = 0;
  let p = 0;

  if(!Array.isArray(formula)) { throw new TypeError("Invalid formula"); }

  for(const clause of formula) {
    if(!Array.isArray(clause)) { throw new TypeError("Invalid clause"); }

    // Empty clause means UNSAT.
    if(clause.length === 0) { return []; }

    m += 1;
    p += clause.length;

    for(const l of clause) {
      if(!Number.isInteger(l)) { throw new TypeError("Invalid literal"); }

      const v = Math.abs(l);
      if(!(v >= 1 && v < 2147483649)) { throw new RangeError("Invalid variable"); }

      if(v > n) { n = v; }
    }
  }

  // Allocate and initialize data structures. L contains the LITERALs of the
  // formula, converted to Knuth's format. S contains the STARTing index of
  // each clause (plus a sentinel value at the end, so we can find the ending
  // index of each clause, too). N contains the NEXT clause that contains
  // the same watched literal as this one (the watched literal is always the
  // first one in a clause), or zero if there is no such clause (it is okay to
  // do this even though zero is a valid index, since the 0th clause will never
  // link to itself). M contains an array of MOVEs for each variable, which
  // acts as a recursion stack and also contains the output.
  const buffer = new ArrayBuffer((p + m + 1 + m + n) * 4);
  const L = new Uint32Array(buffer, 0, p);
  const S = new Uint32Array(buffer, p * 4, m + 1);
  const N = new Uint32Array(buffer, (p + m + 1) * 4, m);
  const M = new Uint32Array(buffer, (p + m + 1 + m) * 4, n);

  for(let i = 0, k = 0; i < formula.length; i++) {
    S[i] = k;

    const clause = formula[i];
    for(let j = 0; j < clause.length; j++, k++) {
      const l = clause[j];
      L[k] = 2 * (Math.abs(l) - 1) + (l < 0);
    }
  }

  S[m] = p;

  for(let i = 0; i < m - 1; i++) {
    for(let j = i + 1; j < m; j++) {
      if((L[S[i]] >>> 1) === (L[S[j]] >>> 1)) {
        N[i] = j;
        break;
      }
    }
  }

  console.log(L);
  console.log(S);
  console.log(N);
  console.log(M);

  // FIXME: Run algorithm B!
  for(let d = 0; d < n; d++) {
  }

  // Convert move array back to the input format.
  const solution = new Array(n);
  for(let i = 0; i < n; i++) {
    solution[i] = (i + 1) * (1 - ((M[i] & 1) << 1));
  }

  return solution;
}

console.log(
  solve([
    [ 1,  2, -3],
    [ 2,  3, -4],
    [ 3,  4,  1],
    [ 4, -1,  2],
    [-1, -2,  3],
    [-2, -3,  4],
    [-3, -4, -1],
    // [-4, 1, -2], // uncommenting this lane will make the problem UNSAT
  ]),
);
