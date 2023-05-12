.read schema.sql
.read views.sql
.import --csv functions.csv functions
.import --csv function_calls.csv function_calls
.import --csv direct_reads.csv direct_reads
.import --csv direct_writes.csv direct_writes
