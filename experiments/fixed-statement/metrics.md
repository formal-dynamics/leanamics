<!-- Output of: python3 run_metrics.py --grok-sessions <Grok session store> --vibe-sessions <Vibe session logs> --json metrics.json runs/voter.json runs/isothermal.json runs/push-pull.json runs/reed-frost.json runs/undecided.json runs/averaging.json runs/median-basics.json runs/two-choices.json -->

| Run | Sessions | Time (m:s) | Time (min) | Span (m:s) | Tool calls | Model calls | Tokens | Cache reads |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| voter | 1 | 31:45 | 32 | 31:45 | 151 | 83 | 10,652,110 (10.7M) | 96.1% |
| isothermal | 1 | 77:35 | 78 | 77:35 | 407 | 168 | 20,015,053 (20.0M) | 94.9% |
| push-pull | 1 | 32:40 | 33 | 32:40 | 179 | 85 | 9,239,665 (9.2M) | 95.8% |
| reed-frost | 1 | 26:26 | 26 | 26:26 | 162 | 87 | 11,379,746 (11.4M) | 97.4% |
| undecided | 1 | 26:33 | 27 | 26:33 | 108 | 57 | 7,044,544 (7.0M) | 93.8% |
| averaging | 1 | 66:10 | 66 | 66:10 | 412 | 167 | 18,709,679 (18.7M) | 95.7% |
| median-basics | 5 | 33:59 | 34 | 123:06 | 132 | 109 | 7,203,264 (7.2M) | n/a |
| two-choices | 4 | 128:29 | 128 | 134:04 | 276 | 224 | 45,763,152 (45.8M) | n/a |

Runs with several sessions (start time in UTC):

```
median-basics:
  1cb992ef  2026-10-02T19:24:27Z   17:09    48 tool calls    3,389,907 tokens
  c07fb0d3  2026-10-02T19:42:28Z    0:12     0 tool calls      196,025 tokens
  7f62cc2d  2026-10-02T21:04:46Z    1:53    21 tool calls      353,583 tokens
  968bc6a1  2026-10-02T21:08:47Z    9:11    31 tool calls    2,195,946 tokens
  0e6de702  2026-10-02T21:22:00Z    5:34    32 tool calls    1,067,803 tokens
two-choices:
  5bc51868  2026-10-03T10:50:19Z   73:43   123 tool calls   25,623,211 tokens
  61f6f09b  2026-10-03T12:04:30Z   12:50    72 tool calls    5,792,599 tokens, continues 5bc51868 after a context compaction
  03943182  2026-10-03T12:20:37Z   39:36    66 tool calls   13,991,099 tokens
  14433dc3  2026-10-03T13:02:04Z    2:19    15 tool calls      356,243 tokens
```
