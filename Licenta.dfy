datatype Problem = Problem(number_of_objects: int, knapsack_capacity: int, costs: seq<int>, weights: seq<int>)

predicate has_positive_values(input: seq<int>)
{
    forall i :: 0 <= i < |input| ==> input[i] > 0
}

predicate is_valid_problem(p: Problem)
{
    |p.costs| == |p.weights| == p.number_of_objects && p.number_of_objects > 0 && p.knapsack_capacity > 0 && 
          has_positive_values(p.costs) && has_positive_values(p.weights)
}

function max(p1: int, p2: int): int
{
    if p1 > p2 then p1 else p2
}

function gain(s: seq<int>, c: seq<int>): int
  requires |s| == |c| 
{
  if |s| == 0 then 0 else s[0] * c[0] + gain(s[1..], c[1..])
}

predicate is_solution(p: Problem, solution: seq<int>, profit: int)
  requires |solution| == |p.costs| 
{
  gain(solution, p.costs) == profit
}

// predicate is_partial_solution(capacity: int, profit: int)
// {

// }

predicate is_optimal_solution(p: Problem, solution: seq<int>, profit: int)
  requires |solution| == |p.costs| 
{
    is_solution(p, solution, profit) // && orice alta solutie are gain < profit
}

method add_sequence(existing_seq: seq<seq<int>>, new_seq: seq<int>, c: int) returns (result: seq<seq<int>>)
  requires |new_seq| == c
  ensures result == existing_seq + [new_seq]
  ensures |result| == |existing_seq| + 1
{
  result := existing_seq + [new_seq];
}

method get_maxim_profit(p: Problem) returns (maxim_profit : int, profits: seq<seq<int>>, solution: seq<int>)
  requires is_valid_problem(p)
  ensures |profits| == p.number_of_objects + 1
  ensures forall k :: 0 <= k <= p.number_of_objects ==> |profits[k]| == p.knapsack_capacity + 1
  // ensures is_solution(p, solution)
{
    profits := []; 
    maxim_profit := 0;
    
    var i := 0;
    while i <= p.number_of_objects 
      invariant 0 <= i <= p.number_of_objects + 1
      invariant |profits| == i
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsack_capacity + 1
    {
        var partial_profits := get_partial_profits(p, profits,i);
        profits := add_sequence(profits, partial_profits, p.knapsack_capacity + 1);
        i := i + 1;
    }

    maxim_profit := profits[p.number_of_objects][p.knapsack_capacity];

    solution := get_knapsack_objects(p, profits, maxim_profit);
}

method get_partial_profits(p: Problem, profits: seq<seq<int>>, i: int) returns (partial_profits: seq<int>)
  requires is_valid_problem(p)
  requires |profits| == i
  requires 0 <= i < p.number_of_objects + 1
  requires forall k :: 0 <= k < i ==> |profits[k]| == p.knapsack_capacity + 1
  ensures |partial_profits| == p.knapsack_capacity + 1
{
        partial_profits := [];
        var j := 0;
        while j <= p.knapsack_capacity
          invariant 0 <= i <= p.number_of_objects + 1 
          invariant 0 <= j <= p.knapsack_capacity + 1
          invariant |partial_profits| == j
        {
          if i == 0 || j == 0 {
              partial_profits := partial_profits + [0];
          } else {
            if p.weights[i - 1] <= j {
              partial_profits := partial_profits + [max(p.costs[i - 1] + profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j])];
            } else {
              partial_profits := partial_profits + [profits[i - 1][j]];
            }
          }
          j := j + 1;
        }
}

method get_knapsack_objects(p: Problem, profits: seq<seq<int>>, maxim_profit: int) returns (solution: seq<int>)
  requires is_valid_problem(p)
  requires |profits| == p.number_of_objects + 1
  requires forall k :: 0 <= k <= p.number_of_objects ==> |profits[k]| == p.knapsack_capacity + 1
  ensures |solution| == p.number_of_objects == |p.weights| == |p.costs|
  // ensures is_solution(p, solution)
{
    solution := [];
    var i := p.number_of_objects;
    var j := p.knapsack_capacity;

    while i > 0 && j >= 0
      invariant 0 <= i <= p.number_of_objects
      invariant 0 <= j <= p.knapsack_capacity
      invariant |solution| == p.number_of_objects - i
      decreases i
      decreases j
    {
      if profits[i][j] == profits[i - 1][j] {
        solution := [0] + solution;
        i := i - 1;
      } else { 
        solution := [1] + solution;
        i := i - 1;
        if j - p.weights[i] >= 0 {
          j := j - p.weights[i];
        }
        
      }
    }
    assert |solution| == |p.weights|;
}

method Main()
{
    var problem: Problem := Problem(number_of_objects := 4, knapsack_capacity := 8, costs := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    var maxim_profit, profits, solution := get_maxim_profit(problem);

    print "Maxim profit: ";
    print maxim_profit;
    print "\n";
}