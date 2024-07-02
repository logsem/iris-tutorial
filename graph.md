```mermaid
graph TD;
  basics --> pure;
  pure --> specs[specifications];
  lang --> specs;
  specs -->  pers[persistently];
  ra --> cst_ra[custom resource algebra];
  ra --> invariants;
  invariants --> conc[concurrency];
  
  conc --> counter;
  conc --> spinlock;
  spinlock --> ticketlock;
  spinlock --> adequacy;

  pers --> linklist[linked list];
  pers -->  ra[resource algebra];

  specs --> later;
  later --> invariants;
  later --> fix[fixpoint];
  linklist --> fix[fixpoint];

  linklist --> arrays;
  conc --> merge;
  arrays --> merge[merge sort];

  ofe;
```