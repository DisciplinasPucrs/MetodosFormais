method Cube(N: int) returns (c: int)
  requires 0 <= N
  ensures c == N*N*N
{
  c := 0;
  var n := 0;
  var k := 1;
  var m := 6;
  while n < N
   invariant 0<=n<=N
   invariant c == n*n*n
   invariant k == 3*n*n + 3*n + 1
   invariant m == 6*n + 6
  {
    c := c + k;
    k := k + m;
    m := m + 6;
    n := n + 1;
  }
}