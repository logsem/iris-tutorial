```mermaid
graph TD;
  basics --> pure;
  pure --> specs[specifications];
  lang --> specs;
  specs --> later;
  later -->  pers[persistently];

  pers -->  ra[resource algebra];

  ra --> cst_ra[custom resource algebra];
  ra --> invariants;
  invariants --> conc[concurrency];
  
  conc --> counter;
  conc --> spinlock;
    spinlock --> ticketlock;
    spinlock --> adequacy;

  pers --> linklist[linked list];
  linklist --> arrays;

  linklist --> fix[fixpoint];

  conc --> merge;
  arrays --> merge[merge sort];
  ofe;
```