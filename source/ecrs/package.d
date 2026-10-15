/// Every ecrs module: `import ecrs;` pulls in all of them, while `static import ecrs.context;` and the like keep each one's names qualified.
module ecrs;

public import ecrs.registry;
public import ecrs.storage;
public import ecrs.context;
public import ecrs.relation;
public import ecrs.system;
