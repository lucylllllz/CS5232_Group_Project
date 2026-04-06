type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost function distinct_chars(s: string, iv: interval): set<char>
  requires 0 <= iv.0 <= iv.1 <= |s|
{
  set i | iv.0 <= i < iv.1 :: s[i]
}

ghost predicate valid_interval_k(s: string, k: int, iv: interval) {
  0 <= k &&
  0 <= iv.0 <= iv.1 <= |s| &&
  |distinct_chars(s, iv)| <= k
}

method lengthOfLongestSubstringKDistinct(s: string, k: int) returns (n: int, ghost best_iv: interval)
  requires 0 <= k
  ensures valid_interval_k(s, k, best_iv)
  ensures length(best_iv) == n
{
  var lo, hi := 0, 0;
  var d := 0; // number of distinct chars in current window
  var count: map<char, int> := map[];
  n, best_iv := 0, (0, 0);

  while hi < |s|
    decreases |s| - hi, |s| - lo
    invariant 0 <= lo <= hi <= |s|
    invariant valid_interval_k(s, k, best_iv)
    invariant length(best_iv) == n
  {
    if s[hi] in count {
      var v := count[s[hi]];
      count := count - {s[hi]};
      count := count + map[s[hi] := v + 1];
      hi := hi + 1;

    } else if d < k {
      count := count + map[s[hi] := 1];
      d := d + 1;
      hi := hi + 1;

    } else {
      var v := count[s[lo]];
      count := count - {s[lo]};
      if v > 1 {
        count := count + map[s[lo] := v - 1];
      } else {
        d := d - 1;
      }
      lo := lo + 1;
    }

  if hi - lo > n {
    assert valid_interval_k(s, k, (lo, hi));
    n := hi - lo;
    best_iv := (lo, hi);
  }
  }
}