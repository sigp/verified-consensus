# `call_db`

This is a lightweight systematisation of the reads and writes of state fields in `process_epoch`.

I started hand-analysing which fields were read and written by each function but this quickly became
tedious when I started expanding "indirect" reads and writes that occur through function calls.
Instead, I've listed just the direct reads, direct writes and call graph in CSV files. These files
are imported into an SQLite database which gives us access to all indirect reads and writes.

Usage:

```
sqlite3
```

```
> .read build.sql
```

## Examples

Which functions read the validator's effective balance?

```sql
SELECT function FROM indirect_reads WHERE field = "validators.effective_balance";
```

```
process_sync_committee_updates
process_slashings
process_rewards_and_penalties
process_registry_updates
process_effective_balance_updates
is_eligible_for_activation_queue
get_next_sync_committee_indices
get_next_sync_committee
get_flag_index_deltas
get_base_reward
```

Which fields does `process_registry_updates` read?

```sql
SELECT field FROM indirect_reads WHERE function = "process_registry_updates";
```

```
finalized_checkpoint
validators.activation_eligibility_epoch
validators.activation_epoch
validators.effective_balance
validators.exit_epoch
```

## Input Format

```
functions.csv
function_calls.csv
direct_reads.csv
direct_writes.csv
```

The `functions.csv` file lists every function name we're interested in. It acts as a safe-guard
against typos in `function_calls.csv`.

The columns of `function_calls.csv` are `caller,callee` where both values are textual function
names. A function is only included in the function call list if it takes the state as an argument
directly. Repeat calls to the same function are not included so each row is a unique tuple. The
function `get_current_epoch` is never included as a callee, because time is frozen and we don't need
to account for its reads/writes.

The columns of `direct_reads.csv` are `caller,field` where caller is a function name and field is a
simplified expression for the field of `state` that is read in the current function. The
simplification ignores indexing, so that `state.validators[i].exit_epoch` is encoded as
`validators.exit_epoch`. Any field of the state that is accessed directly by the function is
included in `direct_reads`. Transitive/indirect reads that occur through other function calls are
NOT included. Repeated reads of the same field are displayed as a single row such that each row is
unique.

The columns of `direct_writes.csv` are similar to `direct_reads`, but for fields written directly by
the function.

## Automation

We could potentially use some automation to extract this data from the Python spec directly, however
writing code to trawl the AST would probably take substantially longer than quickly writing up the
data by hand (all of `process_epoch` only took a few hours).
