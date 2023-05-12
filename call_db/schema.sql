CREATE TABLE functions (
    name TEXT PRIMARY KEY
);

CREATE TABLE function_calls (
    caller TEXT,
    callee TEXT,
    FOREIGN KEY(caller) REFERENCES functions(name),
    FOREIGN KEY(callee) REFERENCES functions(name)
);

CREATE TABLE direct_reads (
    function TEXT,
    field TEXT,
    FOREIGN KEY(function) REFERENCES functions(name)
);

CREATE TABLE direct_writes (
    function TEXT,
    field TEXT,
    FOREIGN KEY(function) REFERENCES functions(name)
);
