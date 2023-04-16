predicate valid_input(input: array<int>)
  reads input
{
    forall i :: 0 <= i < input.Length ==> input[i] >= 0
}

method Max(a: int, b: int) returns (max: int)
  ensures max >= a
  ensures max >= b
  ensures max == a || max == b
{
  if(a < b){
    max := b;
  } else {
    max := a;
  }
}

method Knapsack_problem(n: int, capacity: int, c: array<int>, w: array<int>) returns (maxim_profit : int, solution: array<int>)
  requires n >= 0
  requires capacity >= 0
  requires c.Length == w.Length 
  requires valid_input(w)
  requires valid_input(c)
  requires n == w.Length
  ensures solution.Length == n
{
    var profits := new int[n + 1, capacity + 1];
    
    var i := 0;
    while i <= n 
      invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= capacity
          invariant 0 <= j <= capacity + 1
          invariant 0 <= i <= n + 1
        {
          if i == 0 || j == 0 {
              profits[i, j] := 0;
          } else {
            if w[i - 1] <= j {
                profits[i, j] := Max(c[i - 1] + profits[i - 1, j - w[i - 1]], 
                                  profits[i - 1, j]); 
            } else {
              profits[i, j] := profits[i - 1, j];
            }
          }
          j := j + 1;
        }
      i := i + 1;
    }

    maxim_profit := profits[n, capacity];
    solution := findObjects(n, capacity, w, profits);
}

method findObjects(n: int, capacity: int, w: array<int>, profits: array2<int>) returns (solution: array<int>)
  requires n >= 0
  requires capacity >= 0
  requires valid_input(w)
  requires n == w.Length
  requires profits.Length0 == n + 1
  requires profits.Length1 == capacity + 1
  ensures solution.Length == n
{
   //find the objects that have been added in the knapsack
    solution := new int[n];
    var i := n;
    var j := capacity;
    var k := 0;

    while i > 0 && j > 0 && k < n
      invariant 0 <= i <= n
      invariant 0 <= j <= capacity
      invariant 0 <= k <= w.Length
      decreases i
      decreases j
    {
      if profits[i, j] == profits[i - 1, j] {
        solution[k] := 0;
        i := i - 1;
      } else { 
        solution[k] := 1;
        i := i - 1;
        if j - w[i] >= 0 {
          j := j - w[i];
        }
      }
      k := k + 1;
    }
}

method printSolution(n: nat, maxim_profit: int, solution: array<int>)
  requires n >= 0
  requires n == solution.Length
{
    print "Maxim profit: ";
    print maxim_profit;
    print "\nObjects: ";

    var i := n - 1;
    while i >= 0
      invariant -1 <= i <= n
      decreases i
    {
        print solution[i];
        print " ";
        i := i - 1;
    }
}

method Main()
{
    var number_of_objects: nat := 4; 
    var knapsack_capacity: nat := 8;
    var costs := new int[number_of_objects];
    costs[0] := 1;
    costs[1] := 2;
    costs[2] := 5;
    costs[3] := 6;

    var weights := new int[number_of_objects];
    weights[0] := 2;
    weights[1] := 3;
    weights[2] := 4;
    weights[3] := 5;

    var maxim_profit, solution := Knapsack_problem(number_of_objects, knapsack_capacity, costs, weights);

    printSolution(number_of_objects, maxim_profit, solution);
}