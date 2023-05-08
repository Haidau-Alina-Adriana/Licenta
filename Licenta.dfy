predicate valid_input(input: seq<int>)
{
    forall i :: 0 <= i < |input| ==> input[i] >= 0
}

function max(p1: int, p2: int): int
{
    if p1 > p2 then p1 else p2
}

// predicate is_solution(capacity: int, profit: int)
// {

// }

method add_sequence(existing_seq: seq<seq<int>>, new_seq: seq<int>, c: int) returns (result: seq<seq<int>>)
  requires |new_seq| > 0
  requires |new_seq| == c
  ensures result == existing_seq + [new_seq]
  ensures |result| == |existing_seq| + 1
{
  result := existing_seq + [new_seq];
}

method get_maxim_profit(n: int, capacity: int, c: seq<int>, w: seq<int>) returns (maxim_profit : int)
  requires n >= 0
  requires capacity >= 0
  requires valid_input(w)
  requires valid_input(c)
  requires n == |w| == |c|
{
    var profits: seq<seq<int>> := []; 
    maxim_profit := 0;
    
    var i := 0;
    while i <= n 
      invariant 0 <= i <= n + 1
      invariant |profits| == i
      invariant forall k :: 0 <= k < i ==> |profits[k]| == capacity + 1
    {
        var line: seq<int> := [];
        var j := 0;
        while j <= capacity
          invariant 0 <= j <= capacity + 1
          invariant 0 <= i <= n + 1 
          invariant |line| == j
          invariant forall k :: 0 <= k < i ==> |profits[k]| == capacity + 1

        {
          if i == 0 || j == 0 {
              line := line + [0];
          } else {
            if w[i - 1] <= j {
              line := line + [max(c[i - 1] + profits[i - 1][j - w[i - 1]], profits[i - 1][j])];
            } else {
              line := line + [profits[i - 1][j]];
            }
          }
          j := j + 1;
        }
        profits := add_sequence(profits, line, capacity + 1);
        i := i + 1;
    }

    maxim_profit := profits[n][capacity];
}

method Main()
{
    var number_of_objects: int := 4; 
    var knapsack_capacity: int := 8;

    var costs := [1, 2, 5, 6];
    var weights := [2, 3, 4, 5];

    var maxim_profit := get_maxim_profit(number_of_objects, knapsack_capacity, costs, weights);

    print "Maxim profit: ";
    print maxim_profit;
    print "\n";
}