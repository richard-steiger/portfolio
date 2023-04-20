/***************************************************************************
 * opyright 1990-2023 Ensemble Software Systems, Inc., All Rights Reserved This software is the
 * confidential and proprietary information of Ensemble Software Systems ("Confidential
 * Information"), and contains the valuable trade secrets of Ensemble Software Systems. The software
 * is protected under copyright laws as an unpublished work of Ensemble Software Systems. Notice is
 * for informational purposes only and does not imply publication. You shall not disclose such
 * Confidential Information and shall use it only in accordance with the terms of the license
 * agreement you entered into with Ensemble Software Systems, and for no other use.
 ****************************************************************************/
package net.ess.ebase.core.entities;

import static net.ess.ebase.core.entities.DistributionMachineModel.forwarder;
import static net.ess.ebase.core.entities.DistributionMachineModel.replica;
import static net.ess.ebase.core.entities.PersistenceMachineModel.deleting;
import static net.ess.ebase.core.entities.PersistenceMachineModel.fetching;
import static net.ess.ebase.core.entities.PersistenceMachineModel.storing;
import static net.ess.ebase.lifecycles.LifecycleMachineModel.wired;

import java.util.Collection;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

import net.ess.ebase.core.ResourcePool;
import net.ess.ebase.core.exceptions.AbortException;
import net.ess.ebase.core.exceptions.Assertion;
import net.ess.ebase.core.exceptions.Unfinished;
import net.ess.ebase.core.spaces.Space;
import net.ess.ebase.data.ContainmentAspect;
import net.ess.ebase.events.Event;
import net.ess.ebase.events.EventChannel;
import net.ess.ebase.functions.DomainValueMissingException;
import net.ess.ebase.lifecycles.EntityLifecycleEvent;
import net.ess.ebase.lifecycles.LifecycleState;
import net.ess.ebase.math.automata.StateTransition;
import net.ess.ebase.system.platform.Host;
import net.ess.ebase.system.platform.Site;
import net.ess.ebase.transactions.EntityDeletedEvent;
import net.ess.ebase.transactions.EntityFetchedEvent;
import net.ess.ebase.transactions.EntityMutator;
import net.ess.ebase.transactions.EntityUpdatedEvent;
import net.ess.ebase.transactions.NoteContentUpdatedEvent;
import net.ess.ebase.transactions.Transaction;
import net.ess.ebase.transport.comm.entity.EntityTunnelDecoder;
import net.ess.ebase.transport.comm.entity.EntityTunnelEncoder;
import net.ess.ebase.transport.comm.entity.EntityTunnelSender;
import net.ess.ebase.typeSystem.core.Type;
import net.ess.ebase.typeSystem.core.Version;
import net.ess.ebase.typeSystem.facets.Attribute;
import net.ess.ebase.typeSystem.facets.Facet;
import net.ess.ebase.typeSystem.flags.Flag;
import net.ess.ebase.typeSystem.flags.Flagset;
import net.ess.ebase.typeSystem.structure.EntityType;

/****************************************************************************
 * <code>MetaEntity</code> provide meta-level functionality (and associated state) for entities,
 * including location, type, structure, lifecycles, transport, transactions, p
import nonapi.io.github.classgraph.json.Serializable;ersistence, and
 * object-relational mapping to relational stores.
 * <p>
 * Locations are called <i>spaces</i>, essentially object containers of various kinds, including
 * files, folders, directories, database tables, caches, and the Internet.
 *
 * @author Richard Steiger
 ****************************************************************************/
public class MetaEntity<Id extends Object, Ent extends IEntity>
  extends SpaceLink<Id, Ent>
{
  // ======================================================================
  // Fields
  // ======================================================================
  /** The entity's type, which is also this meta's entityType. */
  public transient EntityType<Ent> entityType;

  /** The entity's home. */
  public transient EntityResidence residence;

  /* Access path to flags. */
  protected transient Flagset flags;
  protected transient long flagMask;
  
  // ======================================================================
  // Constructors and Initializers
  // ======================================================================
  public MetaEntity() {}

  public MetaEntity(Ent entity) {
    this.value = entity;
    entity.meta(this);
    if(types_ != null) {
      types_.injectType(this, value.getClass(), "entityType");
    } else {
      platform_.lifecycles.typeSystemOnline.whenOccurs(this, "finishInit");
    }
    if(kernelState == null)
      platform_.lifecycles.lifecycleManagerOnline.whenOccurs(this, "initKernelState");
  }

  public MetaEntity(EntityType<Ent> valueType, Id key) {
    entityType(valueType);
    key(key);
    createEntity();
    synchKey();
  }

  public MetaEntity(Space space, Id key) {
    traceAlways("why append?");
    nextLink = space.elementFor(this, key);
  }

  public MetaEntity(EntityType<Ent> valueType, Space space) {
    entityType(valueType);
    this.space = space;
    createEntity();
  }

  public MetaEntity(EntityType<Ent> valueType, Space space, Id key) {
    this(valueType, space);
    key(key);
    space.addBinding(this);
  }

  public MetaEntity(int shortcut) {
    this.shortcut = shortcut;
    entityRegistry.shortcutAccess.add(this);
  }

  // ======================================================================
  // Methods
  // ======================================================================
  // ---------------------------
  // Property Access
  // ---------------------------
  /**
   * Returns the attribute having <code>attributeName</code>. Returns null if no such
   * attribute exists.
   */
  public Attribute attribute(String attributeName) {
    return entityType.attribute(attributeName);
  }

  /**
   * Returns the value of the attribute with the given <code>attributeName</code>.
   *
   * @throws IllegalArgumentException if no such attribute exists
   */
  public Object attributeValue(String attributeName) {
    Attribute att = entityType.attribute(attributeName);
    if(att == null) {
      throw new IllegalArgumentException(attributeName);
    } else {
      return att.apply(value);
    }
  }

  /**
   * Returns this type's containment, lazily creating it.
   */
  public ContainmentAspect containment() {
    ContainmentAspect ca = null;
    if(entityType != null) 
      // get containment off entityType if bound
      ca = entityType.containment();

    if(ca == null) {
      // else get the equivalent based on instanceClass
      if(platform_ != null) {
        ca = platform_.containments.containmentFor(value.getClass());
      } else {
        print(":containment blocked on %s", value.getClass().getSimpleName());
      }
    }
    
    return ca;
  }

  /**
   * Returns this meta's described entity.
   */
  public Ent entity() {
    return value;
  }

  /**
   * Returns the entity's class.
   */
  public Class<Ent> entityClass() {
    return entityType != null ? entityType.iClass : (Class<Ent>) value.getClass();
  }

  /**
   * Returns the entity's type binding, returning null if not yet bound.
   * For internal use only.
   */
  public EntityType<Ent> _entityType() {
    return entityType;
  }

  /**
   * Returns the entity's type.
   */
  public EntityType<Ent> entityType() {
    if(entityType == null)
      entityType(types_.applyForEntityType(entityClass()));
    return entityType;
  }

  /**
   * Sets the entity's type. If the type is being changed, applies the new type's 
   * traits to the entity, e.g. propagating (offboard) key to (onboard) primaryId. 
   */
  public MetaEntity entityType(Type<Ent> newType) {
    entityType = (EntityType<Ent>) newType;
    if(key != null)
      entityType.prepared().whenOccurs(this, "setIdFacet");
    return this;
  }

  public void setIdFacet() {
    idFacet = entityType.primaryIdFacet();
    if(key != null)
      synchKey();
  }
  
  /**
   * Sets the entity's identity designated by <code>identityName</code> to <code>identifier</code>.
   */
  public void setId(String identityName, Object identifier) {
    SpaceLink link = this;
    while(link != null) {
      IdStatus status = link.hasIdentity(identityName);
      switch(status) {
        case Has:
          link.setId(identifier);
          return;
        case Hasnt:
          link = link.nextLink;
          continue;
        case Pending:
          link.setId(identifier);
          return;
      }
    }
    newLinkTo(space, (Id) identifier);
  }

  /*
   * Replaces the current entity with <code>newEntity</code>.
   */
  void entityMorphedInto(IEntity newEntity) {
    value = (Ent) newEntity;
    EntityType<Ent> et = types_.applyForEntityType(value.getClass());
    entityType(et);
    // for(MetaEntity link = next; link != null; link = link.next)
    // link.updateMeta(this);
  }

  /**
   * Returns the server on which I reside, or null if I reside in an external residence.
   */
  public synchronized EntityResidence residence() {
    // assign to the localResidence if unassigned
    if(residence == null)
      residence(site());
    return residence;
  }

  /**
   * Returns the host on which the entity resides.
   */
  public Host host() {
    return residence != null ? residence.host() : platform_.host();
  }

  /**
   * Returns sender for forwarding a call to the behavior having <code>buid</code>.
   */
  public EntityTunnelSender getSender(long buid) {
    return residence.sender(this, buid);
  }

  /**
   * Returns sender for forwarding a callto the behavior having <code>behaviorName</code>.
   */
  public EntityTunnelSender getSender(String behaviorName) {
    return residence.sender(this, behaviorName);
  }

  @Override
  public MetaEntity<Id, Ent> primary() {
    return this;
  }

  /**
   * Returns whether this and <code>meta</code> identify the same entity.
   */
  public boolean matchesIdentity(MetaEntity meta) {
    // if(this == meta) {
    // return true;
    // } else if(meta.container != space) {
    // return false;
    // } else {
    // return key.equals(meta.key);
    // }
    throw new Unfinished();
  }

  /**
   * Sets my residence to <code>newResidence</code>. If I already reside at the given site, do
   * nothing. Otherwise, migrate my site to the given container. NOTE: this method MUST be called
   * from within a transaction.
   */
  public void homeBase(Site newResidence) {}

  /**
   * Returns the pool containing the entity, if any.
   */
  public ResourcePool pool() {
    PoolDecoration attachment = getPoolBinding();
    return attachment != null ? attachment.pool : null;
  }

  /**
   * Returns the attached pool metaproperty, if any.
   */
  public synchronized PoolDecoration getPoolBinding() {
    if((decorationMask & MS_IS_POOLED) == 0)
      return null;
    if(decorationChain instanceof PoolDecoration) {
      return (PoolDecoration) decorationChain;
    } else if(decorationChain != null) {
      return findFirstDecoration(PoolDecoration.class);
    } else {
      return null;
    }
  }

  @Override
  public boolean hasValue(Object v) {
    return v != null && v.equals(value);
  }

  // /*
  // * Returns whether activation of the entity is enabled in the current thread.
  // */
  // public static boolean isActivationEnabled() {
  // return activationEnabled.get();
  // }

  /**
   * Sets whether this link is in use.
   */
  public void inUse(boolean inUse) {
    decorationMask = inUse ? decorationMask | MS_IS_IN_USE : decorationMask & ~MS_IS_IN_USE;
  }

  /**
   * Returns whether entity is persistent and has been modified since last synchronized with its
   * storage image.
   */
  public static boolean isDirty() {
    return false;
  }

  /**
   * Returns whether entity is a forwarder.
   */
  public boolean isForwarder() {
    return false;
  }
  
  /**
   * Sets whether the entity is a forwarder.
   */
  public void isForwarder(boolean isForwarder) {}

  /**
   * Returns whether the entity has been fully sketched.
   */
  public boolean isFullySketched() {
    return kernelState.isSketched() && (decorationMask & MS_IN_LIFECYCLE_TRANSITION) == 0;
  }

  /**
   * Returns whether the entity is in use.
   */
  public boolean isInUse() {
    return (decorationMask & MS_IS_IN_USE) != 0;
  }

  /**
   * Returns whether the entity is prepared.
   */
  public boolean isPrepared() {
    return kernelState.isPrepared();
  }

  /**
   * Returns whether the entity is sketched.
   */
  public boolean isSketched() {
    return kernelState.isSketched();
  }

  /**
   * Returns whether the entity is a template.
   */
  public boolean isTemplate() {
    return (decorationMask & MS_IS_TEMPLATE) != 0;
  }

  /**
   * Sets the pool to which the entity belongs.
   */
  public void isTemplate(boolean flag) {
    decorationMask |= MS_IS_TEMPLATE;
  }

  /**
   * Returns whether the entity is sketched.
   */
  public boolean isIn(LifecycleState s) {
    return kernelState.lifecycle == s;
  }

  /**
   * Returns whether the entity uniquizes it's elements, which assumes that the entity is a type or
   * collection.
   */
  public boolean isUniqueizing() {
    return (decorationMask & MS_IS_UNIQUIZING) != 0;
  }

  /**
   * Returns whether the entity is wired.
   */
  public boolean isWired() {
    return kernelState != null && kernelState.isWired();
  }

  /**
   * Returns whether metaEntity is the primary (aka "master") occurrence.
   */
  public boolean isPrimary() {
    return true;
  }

  /**
   * Returns whether entity is registered in the object registry.
   */
  public boolean isRegistered() {
    return registered;
  }

  public void replaceEntity(Ent newEntity, EntityType<Ent> newType) {
    // Space c = space;
    // unregister();
    // value = newEntity;
    // value.meta(this);
    // entityType(newType;
    // hash = -1;
    // setContainer(c);
    throw new Unfinished();
  }

  /**
   * Returns my replication missingResultAction. By default, entities elect the dynamic
   * missingResultAction to allow requesters control.
   */
  public ReplicationPolicy replicationPolicy() {
    return entityType.isImmutable() ? ReplicationPolicy.REPLICATE_DYNAMICALLY
        : value.replicationPolicy();
  }

  /**
   * Sets my residence to <code>newResidence</code>. If I already reside at the given base, do
   * nothing. Otherwise, migrate my base to the given container. NOTE: this method MUST be called
   * from within a transaction.
   */
  public void residence(EntityResidence newResidence) {
    if(residence != newResidence) {
      if(isForwarder())
        throw new AbortException("migration of forwarders not supported.");

      // switch primaryhood
      residence = newResidence;

      if(isRegistered() && newResidence != null) {
        // push the entity to the new base, getting my new identity in
        // the new base register under new ID
        // Object newId = ((Container) newResidence).receiveMigrant(entity);

        if(newResidence.isLocal()) {
          // propagate persistence to new base
          // if(isPrimaryPersistent()) {
          // setResidence((IStorage)storage); }
        } else {
          // add to local registry now that is remote
          synchInvariants();

          // mark now is a replica
          distributionState(replica);

          // propagate persistence to new base
          if(kernelState.isPersistent())
            storePrimary(storage());
        }
      }

      // LATER: mark primaryNode, newId and modifiers updated, so
      // storage will update these fields
    }
  }

  // /**
  // * Sets the entity's event handler, from which events pertaining to the entity are produced.
  // */
  // public void eventHandler(ISink channel) {
  // EventHandlerDecoration p = eventHandlerDecoration();
  // if(channel.isStub()) {
  // removeDecoration(p);
  // decorationMask &= ~MS_HAS_EVENT_HANDLER;
  // } else if(p != null) {
  // p.channel = channel;
  // } else {
  // new EventHandlerDecoration(this, channel);
  // decorationMask |= MS_HAS_EVENT_HANDLER;
  // }
  // }

  /**
   * Sets the entity's event channel, from which events pertaining to the entity are produced.
   */
  public EventChannel eventChannel() {
    EventChannelAttachment attachment = eventChannelAttachment();
    return attachment != null ? attachment.channel : null;
  }

  /**
   * Sets the entity's event channel, from which events pertaining to the entity are produced.
   */
  public void eventChannel(EventChannel channel) {
    EventChannelAttachment attachment = eventChannelAttachment();
    if(channel.isStub()) {
      removeDecoration(attachment);
    } else if(attachment != null) {
      attachment.channel = channel;
    } else {
      new EventChannelAttachment(this, channel);
    }
  }

  /**
   * Returns the entity's primary link from <code>space</code>.
   */
  public SpaceLink linkFrom(Space space) {
    for(SpaceLink c = this; c != null; c = c.nextLink) {
      if(c.space == space)
        return c;
    }
    return null;
  }

  /**
   * Sets the pool to which the entity belongs.
   */
  public void pool(ResourcePool pool) {
    new PoolDecoration(this, pool);
    decorationMask |= MS_IS_POOLED;
  }

  /**
   * Returns the entity's primary containment link.
   */
  public MetaEntity primaryContainment() {
    return value.meta();
  }

  /**
   * Returns the entity's primary container, i.e. the one having the primary link.
   */
  public Space<Id, Ent, SpaceLink<Id, Ent>> primarySpace() {
    return (Space<Id, Ent, SpaceLink<Id, Ent>>) space;
  }

  /**
   * Sets the entity's remote shortcut index.
   * @param s
   */
  public void shortcut(int s) {
    this.shortcut = s;
    entityRegistry.shortcutAccess.add(this);
  }

  /**
   * Returns the entity's site-scoped unique key.
   */
  public Object siteId() {
    throw new Unfinished();
  }

  /**
   * Returns the containing space having class <code>spaceClass</code>.
   */
  public <S extends Space> S spaceOfClass(Class<S> spaceClass) {
    S space = null;
    for(SpaceLink link = this; link != null; link = link.nextLink) {
      if(spaceClass.isInstance(link.space)) {
        space = (S) link.space;
        break;
      }
    }
    return space;
  }

  /**
   * Returns the entity's version.
   */
  public Version version() {
    VersionDecoration attachment = versionDecoration();
    return attachment != null ? attachment.version : null;
  }

  /**
   * Sets the entity's version.
   */
  public void version(Version version) {
    VersionDecoration v = versionDecoration();
    if(v != null) {
      v.version = version;
    } else {
      new VersionDecoration(this, version);
    }
  }

  // ---------------------------
  // Lifecycle Management
  // ---------------------------
  /**
   * Assigns a serial key to the entity.
   */
  public SerialIdDecoration assignSerialId() {
    SerialIdDecoration serId = serialIdDecoration();
    if(serId == null)
      serId = new SerialIdDecoration(this);
    key((Id) serId);
    return serId;
  }

  /**
   * Return a clone of this object after invoking its finishClone() method hierarchy.
   */
  public MetaEntity clone(Ent entityClone) {
    MetaEntity m = (MetaEntity) clone();
    m.value = entityClone;
    return m;
  }

  /**
   * Deallocates this component, returning it to its pool.
   */
  public void deallocate() {
    if((decorationMask & MS_IS_POOLED) > 0)
      getPoolBinding().pool.returnToPool(value);
  }

  /**
   * Returns a clone of the entity, including invoking its finishClone() method hierarchy.
   */
  public Ent entityClone() {
    return (Ent) value.clone();
  }

  /*
   * Finishes the cloning operation inside the clone.
   */
  public void finishCloning() {
    SerialIdDecoration sidd = serialIdDecoration();
    super.finishCloning();
    registered = false;
    nextLink = null;
    registryBucketChain = null;
    if(sidd != null) {
      removeDecoration(sidd);
      assignSerialId();
    }
  }

  @Override
  public void finishInit() {
    if(entityType == null)
      entityType(types_.apply(value.getClass()));
  }
  
  /**
   * Callback to synchronize persistence after state machines are initialized.
   */
  public void doMetaInitAction() {
    synchPersistence();
  }

  /**
   * Purge the entity and all proxies from the cache.
   */
  public void purge() {
    if(kernelState.isRemote()) {
      try {
        purgePrimary();
      } catch(DomainValueMissingException e) {
        // ignore if someone beat the entity to it
      }
    }
    unregister();

    // disconnect all event sinks
    EventChannel channel = eventChannel();
    if(channel instanceof EventChannel)
      ((EventChannel) channel).disconnect();
  }

  /**
   * Forward a purge request to my base.
   *
   * @forward
   */
  public void purgePrimary() {
    purge();
  }

  /**
   * Synchronizes the value's onboard identifier and offboard key.
   */
  public void synchKey() {
    if(value == null)
      return;

    // if idFacet hasn't been set, try setting it from the key's class
    if(idFacet == null) {
      if(entityType != null)
        idFacet = entityType.idFacetFor(key);

      // if that didn't work, treat call as no-op
      if(idFacet == null)
        return;
    }

    // if id state is onboard, and not the key, set the id
    if(!idFacet.isMetaKeyFacet() && idFacet.apply(value) != key) {
      if(idFacet.canReturn(key)) {
        idFacet.put(value, key);
      } else {
        idFacet = entityType.idFacetFor(key);
        if(!idFacet.isMetaKeyFacet())
          idFacet.put(value, key);
      }
    }
  }
  
  /**
   * If the space and key are bound, computes the hash code, sets the homebase, assigns a shortcut
   * (if needed); if entity is attached, inserts this meta into the object registry and space,
   * and if the entityType has an extent, inserts entity into the extent. Returns whether insertion
   * occurred.
   * <p>
   * Note: this method is "quasi-idempotent": it can be called on a meta that's a lookup probe
   * (hence having no entity), and if converted to a proxy, then materialized, this method is then
   * called on the same meta (with the materialized entity now bound), at which point it performs
   * the insertions.
   */
  public boolean synchInvariants() {
    if(residence == null)
      return false;

    // assign a shortcut if unassigned and entity isn't a container
    if(shortcut == 0 && !(value instanceof Site))
      shortcut = EntityRegistry.getUniqueInt();

    // insert this into <code>entityRegistry</code>
    entityRegistry.add(this);

    return true;
  }

  /**
   * Propagates persistence from primaryContainer
   */
  public void synchPersistence() {
    if(nextLink != null) {
      Assertion.check(space != null);
      if(space.isStored() && !isStored())
        markPersistent();
    }
  }

  /**
   * Remove this metaobject from the registry.
   */
  public synchronized void unregister() {
    if(registered) {
      if(entityType != null)
        entityType.unregisterInstance(value);
      if(entityRegistry != null)
        entityRegistry.remove(this);
      super.unregister();
    }
  }

  // ---------------------------
  // MetaEntity Creation
  // ---------------------------
  /**
   * Creates and returns a new entity instance of <code>type</code>, having <code>key</code>, and
   * contained in <code>space</code> (if non-null).
   */
  public static <F extends IEntity> F newEntity(EntityType<F> valueType, Object key, Space space) {
    return (F) new MetaEntity(valueType, space, key).value;
  }

  /**
   * Creates and returns a new entity instance of <code>entityType</code>, having <code>key</code>,
   * contained in <code>space</code> (if non-null), and having <code>modifiers</code>. If
   * <code>space != null</code>, the entity is marked as a base storage proxy, else as simply a
   * base.
   */
  public static <F extends IEntity> F NewProxy(EntityType<F> valueType, Object key, Space space) {
    MetaEntity link = new MetaEntity(valueType, space, key);
    return (F) link.newProxy(key);
  }

  // ---------------------------
  // Entity Creation
  // ---------------------------
  /*
   * Creates and binds a raw (uninitialized) entity.
   */
  public Ent createEntity() {
    Ent entity = entityType.instance();
    entity.meta(this);
    if(key != null)
      entity.pidChanged(key);
    value = entity;
    return entity;
  }

  /**
   * Converts this meta into a storage proxy with <code>newKey</code>.
   */
  public Ent newProxy(Id newKey) {
    key(newKey);
    markStorageProxy();
    createEntity();
    return value;
  }

  /**
   * Creates and returns an instance of <code>entityType</code> attached to this meta, and having
   * having the <code>distribution</code> distribution.
   */
  public Ent newRaw(EntityType valueType, DistributionState distribution) {
    entityType(valueType);
    distributionState(distribution);
    createEntity();
    return value;
  }

  // ---------------------------
  // Flag Management
  // ---------------------------
  /*
   * Returns the bound flagset, lazily creating it.
   */
  public Flagset flags() {
    if(flags == null)
      flags = platform_.flagManager.flagsetFor(flagMask);
    return flags;
  }

  /**
   * Returns whether all <code>flags</codes> are contained in the flagset.
   */
  public boolean hasAll(Flag... flags) {
    for(Flag t : flags) {
      if(!t.test(flagMask))
        return false;
    }
    return true;
  }

  public void inherit(MetaEntity parent) {
    if(flags != parent.flags && parent.flags != null) 
      plus(parent.flags);
  }

  public boolean isAtom() {
    return ATOM.test(flagMask);
  }

  /**
   * Sets the flag mask to <code>m</code>.
   */
  public void mask(long m) {
    flagMask = m;
    flags = platform_.flagManager.flagsetFor(flagMask);
  }

  /**
   * Adds <code>flags</code> into the mask.
   */
  public MetaEntity plus(Flag... flags) {
    long m = flagMask;
    for(Flag t : flags) 
      m |= t.mask;
    mask(m);
    return this;
  }

 /**
   * Adds flagset <code>s</code> into the mask.
   */
  public MetaEntity plus(Flagset s) {
    plus(s.mask);
    return this;
  }

  /**
   * Adds <code>bits</code> into the mask.
   */
  public MetaEntity plus(long bits) {
    mask(flagMask | bits);
    return this;
  }

  /**
   * Removes <code>bits</code> from the mask.
   */
  public MetaEntity minus(Flag f) {
    minus(f.mask);
    return this;
  }

 /**
   * Removes <code>bits</code> from the mask.
   */
  public MetaEntity minus(Flagset s) {
    minus(s.mask);
    return this;
  }

  /**
   * Removes <code>bits</code> from the mask.
   */
   public MetaEntity minus(long bits) {
     mask(flagMask & ~bits);
     return this;
   }

   /**
    * If <code>flag</code>, then Sets <code>bits</code>, else clears.
    */
   public MetaEntity setMask(boolean flag, Flag f) {
     return flag ? plus(f) : minus(f);
   }

  // ---------------------------
  // Decoration Management
  // ---------------------------
  /**
   * Returns the attached serial id decoration.
   */
  public SerialIdDecoration serialIdDecoration() {
//    if((decorationMask & MS_HAS_SERIAL_ID) == 0)
//      return null;
    return decorationChain instanceof SerialIdDecoration
        ? (SerialIdDecoration) decorationChain
        : findFirstDecoration(SerialIdDecoration.class);
  }

  /**
   * Returns the attached version decoration.
   */
  public VersionDecoration versionDecoration() {
    if((decorationMask & MS_HAS_VERSION) == 0)
      return null;
    return decorationChain instanceof VersionDecoration ? (VersionDecoration) decorationChain
        : findFirstDecoration(VersionDecoration.class);
  }

  // ---------------------------
  // Identity Management
  // ---------------------------
  /**
   * Returns the entity's primary key, as follows:
   * <ul>
   * <li>if the key is set, primaryId = key;
   * <li>else the type is bound, fetches the piFacet, then
   * <ul>
   * <li>if the facet's returned, applies it to the value, binding the result to the key,
   * <li>else returns the key returns the key if bound, else the primary link's key, else the value
   * of the entity's primary idFacet.
   */
  public Id key() {
    Id k = key;

    // return primaryId if key is unbound
    // try getting value of primaryIdFacet
    if(k == null && entityType != null) {
      Facet piFacet = entityType.primaryIdFacet();
      // check whether this just comes back here
      if(piFacet != null && !piFacet.isMetaKeyFacet())
        k = (Id) piFacet.apply(value);
    }

    // update key with new value
    if(k != null && k != key)
      key((Id) k);
    return key;
  }

  /**
   * Adds <code>newId</code> as an alternate identifier, in the existing container. Nulls are ignored.
   */
  public void addId(Id newId) {
    if(newId == null)
      return;
    if(key == null) {
      key(newId);
    } else if(space != null) {
      space.put(newId, value);
    }
  }

  // ---------------------------
  // Insertion
  // ---------------------------
  /**
   * Stores the entity in the designated space. This is a support method that is invoked from one of
   * my remote proxies, hence entity is always a primary. Returns whether entity is already
   * persistent, hence store is a no-op.
   *
   * @forward
   */
  public boolean storePrimary(Space space) {
    throw new AbortException("storing remote primary unsupported");
  }

  // ---------------------------
  // Deletion
  // ---------------------------
  /**
   * Deletes the entity from all of its containments, cascading to dependent referencers and
   * referencees. 
   * <p>
   * If the entity is a remote proxy, deletes both the entity, and its base; the resulting event
   * will trigger all other proxies to be deleted in secondary transactions.
   * <p>
   * Performs the operation in <code>transaction</code> if non-null, else performs it in its own
   * transaction.
   */
  public synchronized void deleteIn(Transaction transaction) {
    if(isRemote()) {
      // LATER: handle remote proxies
      throw new Unfinished();
    } else if(!isInTransition(deleting)) {
      EntityMutator mutator = mutator(transaction, space);
      for(SpaceLink link = this; link != null; link = link.nextLink) {
        if(link.space() != null)
          mutator.addEvent(new EntityDeletedEvent());
      }
    }
  }

  // ---------------------------
  // Synchronization
  // ---------------------------
  /**
   * Fetches the entity's lifecycleState from its storage image, overriding its lifecycleState at the
   * point of the call.
   */
  public void refreshContents() {
    storage().doFetch(value);
  }

  /**
   * Attempts to fix invariants if entityType is wired.
   */
  public void repairInvariants() {
    Assertion.check(entityType != null);
    if(!entityType().isFullySketched())
      entityType.ensureSketched();
    if(entityType.isFullySketched()) {
      synchInvariants();
    } else {
      value.traceAlways("$$$$$$$$$ unable to synch invariants, since %s isn't sketched", entityType);
    }
  }

  /**
   * Ensures that the entity's content is up-to-date with respect to any underlying stored and/or
   * remote images.
   */
  public synchronized void readState() {
    if(kernelState.needsToBeFetched() && transition() != fetching) {
      mutator().doAtomically(m -> m.addEvent(new EntityFetchedEvent()));
    }
  }

  /**
   * Ensures that entity's kernelState is up-to-date with respect to any underlying stored and/or remote
   * images.
   */
  public synchronized void synchKernelState() {
    if(kernelState == null)
      return;
    StateTransition transition = transition();
    EntityMutator mutator = null;
    if(kernelState.needsToBeFetched() && transition != fetching) {
      mutator = mutator();
      mutator.addEvent(new EntityFetchedEvent());
      mutator.transaction.commit();
    } else if(kernelState.isDirty() && transition != storing) {
      // mutator = getWriteCoordinator(null);
      // mutator.addEvent(new EntityFetchedEvent(next));
      // mutator.transaction.commit();
      throw new Unfinished();
    }
  }

  // ---------------------------
  // Updating
  // ---------------------------
  /**
   * Atomically updates the facet designated by <code>facetName</code> from <code>oldValue</code> to
   * <code>newValue</code>, including performing any compound updates (e.g. updating relationships).
   */
  public void updateFacet(String facetName, Object oldValue, Object newValue) {
    // if both old and new values are null, bail
    if(oldValue == null && newValue == null)
      return;

    // if old and new values are equivalent, bail
    if(oldValue != null && oldValue.equals(newValue))
      return;

    // bail if already in target state
    if(kernelState.lifecycle != wired)
      goTo(wired);

    Facet facet = entityType.facet(facetName);
    if(facet == null)
      throw new AbortException("facet doesn't exist: %s.%s", entityType.baseName(), facetName);

    if(isRegistered() && facet.isPersistable()) {
      mutator().doAtomically(m -> facet.updateEntity(value, oldValue, newValue, false, m.transaction));
    } else {
      facet.updateEntity(value, oldValue, newValue, false, null);
    }
  }

  // ---------------------------
  // Transaction Management
  // ---------------------------
  /**
   * Atomically applies <code>event</code> to entity.
   */
  public void applyEvent(EntityLifecycleEvent event) {
    if(isRegistered()) {
      mutator().doAtomically(m -> m.addEvent(event));
    } else {
      event.distribute();
    }
  }

  /**
   * Notifies the current transaction that the value of the attribute having 
   * <code>attributeName</code> has been updated from <code>oldValue</code> to
   * </code>newValue</code>.
   */
  public void attributeUpdated(String attributeName, Object oldValue, Object newValue) {
    applyEvent(new EntityUpdatedEvent(attributeName, oldValue, newValue));
  }

  /**
   * Schedule the invocation of the method designated by <code>selector</code> on entity. If
   * currently in a transaction, schedule the invocation to occur when the transaction commits,
   * otherwise, perform it now. When scheduled as part of a transaction, the invocation is performed
   * prior to any other commit processing. Multiple requests for the same invocation are folded into
   * a single request, hence the term "compute" instead of "invoke". When performed, the invocation
   * is allowed to schedule additional such requests to be performed within this same transaction's
   * commit operation.
   */
  public void computeOnCommit(String selector) {
    // get the current transaction, if any
    // EntityMutator mutator = mutatorOn(space);
    // Transaction t = mutator.transaction;
    //
    // // if in an orginating transaction, schedule the command's lifecycle
    // // at commit time, else just invoke it now
    // if(t != null && t.isOriginator()) {
    // t.computeOnCommit(new Command(entity, selector));
    // } else {
    // invokeMethod(selector);
    // }
    throw new Unfinished();
  }

  /**
   * Disable invoking any transaction resource methods during commit processing on entity in the
   * current transaction.
   *
   * @forward
   */
  public void disableResourceCommits() {
    mutator().disableResourceCommits();
  }

  /**
   * Posts an entityUpdatedEvent on entity in the given transaction.
   */
  public Transaction postUpdate(String attributeName, Object oldValue, Object newValue) {
    // EntityUpdatedEvent e = new EntityUpdatedEvent(value, entityType.attribute(attributeName),
    // oldValue, newValue);
    // if(isRegistered()) {
    // Transaction t = getCurrentTransaction();
    // getWriteCoordinator(t).addEvent(e);
    // return t;
    // } else {
    // e.distribute();
    // return null;
    // }
    throw new Unfinished();
  }

  /**
   * Releases the current read or write lock on entity, if any.
   */
  public synchronized void unlock() {
    Assertion.check(decorationChain instanceof EntityMutator);
    ((EntityMutator) decorationChain).unlock();
  }

  // ---------------------------
  // Flows Support
  // ---------------------------
  /**
   * Returns the set of children in storage for entity as parent.
   */
  public Collection fetchChildren(String childrenAttributeName) {
    // sync();

    // goTo(wired);

    if(space.isStorage()) {
      return space.fetchChildren(value, childrenAttributeName);
    } else {
      return (Collection) attribute(childrenAttributeName).out().instance();
    }
  }

  // ---------------------------
  // Distribution control
  // ---------------------------
  /**
   * Become a forwarder.
   */
  public MetaEntity becomeForwarder() {
    distributionState(forwarder);
    return this;
  }

  /**
   * Become a replica based on the new residence. This method implicitly assumes that a primary
   * object having the same key as entity exists on the newResidence.
   */
  public MetaEntity becomeReplica(EntityResidence newResidence) {
    if(isPrimary())
      distributionState(replica);

    // update its residence, which reindexes in the registry
    residence(newResidence);
    return this;
  }

  /**
   * Become a replica based on the new residence. This method implicitly assumes that a primary
   * object having the same key as entity exists on the newResidence.
   */
  public MetaEntity becomeReplica(Site newResidence) {
    if(isPrimary())
      distributionState(replica);

    // update its residence, which reindexes in the registry
    residence(newResidence);
    return this;
  }

  /**
   * Replicate entity.
   */
  public void replicate() {
    // if(isForwarder()) replicate(1);
  }

  /**
   * Imports the transitive closure rooted at the entity. The closure is bounded by the given number
   * of levels, with negative levels meaning unbounded. Implementation note: replicate() is the
   * public interface. It in turn asks the base sendReplica, which encodes its own closure in the
   * receiver; this encoding is returned as the reply of the request. When decoded, the closure is
   * materialized, thereby performing the replication. NOTE that a messenger is passed into
   * sendReplica; this is by special arrangement with the method generator, which treats such args
   * specially, passing the messenger instead of decoding the args from the messenger and passing
   * them.
   */
  public void replicate(int levels) {
    if(kernelState.isRemote()) {
      // getHomeBase().sendReplica( value, null, levels, null);
      throw new Unfinished();
    }
  }

  /**
   * Imports the transitive closure rooted at the value of the given attribute. The closure is
   * bounded by the given number of levels, with negative levels meaning unbounded.
   */
  public Object replicateAttribute(String attributeName, int levels) {
    /*
     * if(isRemoteProxy()) { print(this+" requesting replica of "+attributeName);
     * EntityTunnelDecoder resultStream = getHomeBase().sendReplica(value, attributeName, levels,
     * null); Object result = resultStream.next(); resultStream.free(); return result; } else {
     * return null; }
     */
    return null;
  }

  // ---------------------------
  // Event Processing
  // ---------------------------
  /**
   * Creates an event connection to the event <code>channel</code>. Ignored if
   * <code>channel.isStub()</code>. This method will replace the current channel binding with an event
   * channel if necessary to properly handle fan-out.
   */
  public void connectTo(EventChannel<Event> channel) {
    if(channel.isStub())
      return;
    EventChannelAttachment attachment = eventChannelAttachment();
    if(attachment != null) {
      EventChannel currentChannel = attachment.channel;
      if(currentChannel == null) {
        attachment.channel = channel;
      } else {
        EventChannel ch = null;
        if(currentChannel instanceof EventChannel) {
          ch = (EventChannel) currentChannel;
        } else {
          ch = new EventChannel();
          attachment.channel = ch;
        }
        ch.connectTo(channel);
      }
    } else {
      eventChannel(channel);
    }
  }

  /**
   * Disconnect the event connection from the entity's eventChannel to the given channel.
   */
  public synchronized void disconnectFrom(EventChannel<Event> channel) {
    EventChannelAttachment attachment = eventChannelAttachment();
    if(attachment != null) {
      EventChannel currentChannel = attachment.channel;
      if(channel == currentChannel) {
        eventChannel(null);
      } else if(currentChannel instanceof EventChannel) {
        EventChannel ch = (EventChannel) currentChannel;
        ch.disconnectFrom(channel);
        if(ch.getSinks() == null || ch.getSinks().isEmpty())
          eventChannel(null);
      }
    }
  }

  /**
   * Forwards the given <code>event</code> to via the event channel, if one is bound.
   */
  public void forwardEvent(Event event) {
    EventChannel channel = eventChannel();
    if(channel != null)
      channel.accept(event);
  }

  /**
   * Receives notification that the entity is a space whose contents have changed.
   */
  public void noteContentsChanged() {
    // if end of chain, done
    if(nextLink == null)
      return;

    // skip if already being written
    if(isBeingWritten())
      return;

    // if persistent and directly stored (space is storage), schedule an EntityAlteredEvent
    // to trigger rewriting the image
    Space space = nextLink.space;

    // handle Universe case
    if(space == value)
      return;

    if(isPersistent() && space.isStorage()) {
      mutator().doAtomically(m -> m.addEvent(new NoteContentUpdatedEvent()));
    }

    // otherwise, propagate the notice up the link hierarchy
    else {
      if(space != null) {
      space.meta().noteContentsChanged();
      } else {
        trap =2 ;
      }
    }
  }

  // ---------------------------
  // Flows
  // ---------------------------
  /**
   * Decodes this metaentity's lifecycleState from the stream.
   * PENDING generation via augmentation.
   */
  public MetaEntity decode(EntityTunnelDecoder in) {
    // entityType((EntityType<Ent>) in.readTypeByName();
    // primaryId(in.readStruct());
    // addTo((Space) in.readStruct());
    // addTo((Storage) in.readStruct());
    // propertyMask = in.readInteger();
    //
    // // TODO: following cast is a patch; the principled fix is to change the signature
    // MetaEntity registeredMeta = (MetaEntity)
    // entityRegistry.uidAccessPath.findMetaMatchingId(this);
    // return registeredMeta != null ? registeredMeta : this;
    throw new Unfinished();
  }

  /**
   * Encodes the entity's lifecycleState on the stream.
   */
  public void readEntityState(EntityTunnelDecoder in) {
    if(entityType.isImmutable()) {
      entityType.structure().decode(value, in);
    } else {
      value.decodeState(in);
    }
  }

  /**
   * Encodes the entity's lifecycleState on the stream.
   */
  public void encodeEntityState(EntityTunnelEncoder out) {
    encodeReference(out);
    if(entityType.isImmutable()) {
      entityType.structure().encode(value, out);
    } else {
      value.encodeState(out);
    }
  }

  /**
   * Writes the entity's reference on the stream.
   */
  public void encodeReference(EntityTunnelEncoder out) {
    // encode spaces via guids
    if(value instanceof Site) {
      out.encodeContainer((Site) value);
    } else {
      out.encodeType(entityType);
      out.encodeResidence(residence);
      out.writeInteger(decorationMask);

      // encode the primaryId, optimizing the common case when it's an integer
      Object primaryId = value.primaryId();
      if(primaryId instanceof Long) {
        out.encodeLong(((Long) primaryId).intValue());
      } else {
        out.encode(primaryId);
      }
    }
  }

}

