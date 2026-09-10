/// `import ecrs;` pulls in every module; `import ecrs.context;` etc. still
/// works for module-qualified access only.
module ecrs;

public import ecrs.registry;
public import ecrs.storage;
public import ecrs.context;
public import ecrs.relation;
public import ecrs.system;
