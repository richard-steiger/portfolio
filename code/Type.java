package net.ess.ebase.typeSystem.core;

import static net.ess.ebase.typeSystem.core.TypeComparisonKind.EQUAL;
import static net.ess.ebase.typeSystem.core.TypeComparisonKind.INCOMPARABLE;
import static net.ess.ebase.typeSystem.core.TypeComparisonKind.SUB;
import static net.ess.ebase.typeSystem.core.TypeComparisonKind.SUPER;
import static net.ess.ebase.typeSystem.metatypes.Metatype.Any_;
import static net.ess.ebase.typeSystem.metatypes.Metatype.Connective_;
import static net.ess.ebase.typeSystem.metatypes.Metatype.Reference_;
import static net.ess.ebase.util.BasicUtils.uncapitalize;

import java.io.Serializable;
import java.lang.annotation.Annotation;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.TypeVariable;
import java.text.Format;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import io.github.classgraph.ClassGraph;
import io.github.classgraph.ClassInfoList;
import io.github.classgraph.ScanResult;
import net.ess.ebase.core.Any;
import net.ess.ebase.core.Component;
import net.ess.ebase.core.EObject;
import net.ess.ebase.core.INamed;
import net.ess.ebase.core.entities.Entity;
import net.ess.ebase.core.entities.IEntity;
import net.ess.ebase.core.entities.IdentityAspect;
import net.ess.ebase.core.exceptions.AbortException;
import net.ess.ebase.core.exceptions.Assertion;
import net.ess.ebase.core.exceptions.Unfinished;
import net.ess.ebase.core.spaces.Space;
import net.ess.ebase.data.ContainmentAspect;
import net.ess.ebase.data.ECollection;
import net.ess.ebase.data.EqualityMap;
import net.ess.ebase.data.IdentitySet;
import net.ess.ebase.data.Sequence;
import net.ess.ebase.data.UniqueOrderedAccumulator;
import net.ess.ebase.execution.Command;
import net.ess.ebase.execution.control.Condition;
import net.ess.ebase.execution.control.LifecycleStateCondition;
import net.ess.ebase.flows.EndOfFlowException;
import net.ess.ebase.flows.IntFlow;
import net.ess.ebase.flows.Source;
import net.ess.ebase.functions.Function;
import net.ess.ebase.graphs.Graph;
import net.ess.ebase.graphs.GraphElementGroup;
import net.ess.ebase.graphs.Node;
import net.ess.ebase.langs.commonCore.Identifier;
import net.ess.ebase.lifecycles.EntityBuilder;
import net.ess.ebase.lifecycles.LifecycleState;
import net.ess.ebase.math.foundations.IncrementalSet;
import net.ess.ebase.math.foundations.IntersectionSet;
import net.ess.ebase.math.foundations.UnknownSetExtentException;
import net.ess.ebase.models.Model;
import net.ess.ebase.structures.IStructure;
import net.ess.ebase.system.stats.TypeStats;
import net.ess.ebase.text.TextFlow;
import net.ess.ebase.transport.storage.files.IFyle;
import net.ess.ebase.typeSystem.MetaInterpreter;
import net.ess.ebase.typeSystem.TypeExpression;
import net.ess.ebase.typeSystem.annotations.BootPrintable;
import net.ess.ebase.typeSystem.annotations.NonInstantiable;
import net.ess.ebase.typeSystem.annotations.PrimaryIdentity;
import net.ess.ebase.typeSystem.behavior.Behavior;
import net.ess.ebase.typeSystem.behavior.BehaviorFinder;
import net.ess.ebase.typeSystem.behavior.BehaviorRegistry;
import net.ess.ebase.typeSystem.extents.StrongTypeExtent;
import net.ess.ebase.typeSystem.extents.TypeExtent;
import net.ess.ebase.typeSystem.facets.Attribute;
import net.ess.ebase.typeSystem.facets.AttributeFlow;
import net.ess.ebase.typeSystem.facets.Facet;
import net.ess.ebase.typeSystem.facets.FacetFlow;
import net.ess.ebase.typeSystem.facets.FieldFlow;
import net.ess.ebase.typeSystem.flags.Flag;
import net.ess.ebase.typeSystem.flags.FlagManager;
import net.ess.ebase.typeSystem.functions.FunctionAspect;
import net.ess.ebase.typeSystem.metatypes.Metatype;
import net.ess.ebase.typeSystem.parameterization.TypeParameter;
import net.ess.ebase.typeSystem.parameterization.TypeParameterSignature;
import net.ess.ebase.typeSystem.registration.TypeAddress;
import net.ess.ebase.typeSystem.registration.TypeBuilder;
import net.ess.ebase.typeSystem.registration.TypeKind;
import net.ess.ebase.typeSystem.registration.TypePackage;
import net.ess.ebase.typeSystem.scopes.ITypeScope;
import net.ess.ebase.typeSystem.structure.EntityType;
import net.ess.ebase.typeSystem.structure.ITypeAspect;
import net.ess.ebase.typeSystem.structure.StructureAspect;
import net.ess.ebase.typeSystem.structure.StructureType;
import net.ess.ebase.typeSystem.structure.TypeAncestryTraversal;
import net.ess.ebase.typeSystem.structure.TypeAspectSet;
import net.ess.ebase.typeSystem.structure.TypeInheritance;
import net.ess.ebase.typeSystem.translation.FormattingTranslator;
import net.ess.ebase.typeSystem.translation.IValueTranslator;
import net.ess.ebase.typeSystem.translation.TranslatorRegistry;
import net.ess.ebase.util.ReflectionUtils;

/****************************************************************************
 * <code>Type</code>s are ebase's primary metadata, describing structure and behavior
 * of all objects. 
 * <p>
 * Types are specializations of models, which in turn are digraph nodes. Types are 
 * linked via several kinds of edges to form comprehensive <s>system type graphs</s> (aka
 * "data models" or "object models" in SysML or UML terminology). Edge types include
 * <ul>
 * <li><code>TypeInheritance</code> - representing all inheritances between both concrete
 * and interface types</li>
 * <li><code>Facet</code> - representing types' instances' properties, both state variables
 * and behaviors</li>. 
 * </ul>
 * <p>
 * The <s>inheritance type graph</s>, whose edges are just <code>TypeInheritance</code>s, forms 
 * a lattice structure, whose top (supremum) is <code>Any</code>, and whose bottome (infemum)
 * is <code>NothingType</code>. 
 *
 * @author Richard Steiger
 ****************************************************************************/
@PrimaryIdentity("primaryId:net.ess.ebase.typeSystem.registration.TypeAddress")
@BootPrintable
@NonInstantiable
public class Type<T> 
  extends Model<T> 
  implements TComparable<Type>, IValueTranslator, TypeExpression
{
  // ======================================================================
  // Fields
  // ======================================================================
  /*----- constants -----*/
  /* Illegal tag values. */
  private static Flag[] ILLEGAL_TYPE_TAGS = new Flag[] {FACET, LIST, IMMUTABLE, CONNECTIVE, COMPONENT, GRAPH,
      JCOLLECTION, ATOM, ATTRIBUTE, FUNCTION, MAP, ARRAY};

  /* Tags that are illegal for types. */
  private static Set<Flag> illegalTags = new HashSet();

  /** Typecode extending java.sql.Types denoting classes. */
  static final int TYPE_CLASS = 3000;

  /** Typecode extending java.sql.Types denoting lists. */
  static final int TYPE_LIST = 3001;

  /** Typecode extending java.sql.Types denoting enums. */
  static final int TYPE_ENUM = 3002;

  /** Typecode extending java.sql.Types denoting maps. */
  static final int TYPE_MAP = 3003;

  /*----- static state -----*/
  private static boolean showFlags = false;

  /* A sentinel extent indicating that no extent is bound on this type's supertype chain. */
  protected static TypeExtent nullExtent; // = new StrongTypeExtent();

  /* The function aspect yielded by non-function types. */
  public static final FunctionAspect nullFunctionAspect = new FunctionAspect();

  /* The flagGroup type, shared by all types. */
  public static FlagManager groupType;

  protected static TypeComparator typeComparator;

  /* The empty structure aspect, which is the structure of all non-structure types. */
  protected static StructureAspect emptyStructure = new EmptyStructureAspect();

  /*----- public state -----*/
  /** The class of this type's instances. */
  public Class<T> iClass;

  /** This type's metatype. */
  public Metatype metatype;

  /* This type's supertype (aka primary ancestor). */
  protected Type supertype;

  /* This type's subtype closure. */
  protected IdentitySet<Type> allSubtypes;
  
  /* This type's signature. */
  /** Maps types to aspects. */
  protected TypeAspectSet aspects;

  public TypeParameterSignature signature;

  /* Map from parameter name to the designated inbound parameter. */
  protected Map<String, TypeParameter> inboundParameters;

  /** The registry of this type's behaviors. */
  protected transient BehaviorRegistry behaviors;

  /*----- utility feature state -----*/
  /**
   * This type's extent, containing the registered instances of this type when it's an
   * entityType. @readOnly, @friendOf SpaceBinding<In,T>
   */
  public transient TypeExtent extent;

  /* This type's translator between this type's instances and external text encodings. */
  protected IValueTranslator translator;

  /*----- internal construction-related state -----*/
  /* This type's builder. */
  public TypeBuilder builder;

  /* Chain link on which variants are linked off base. */
  protected Type variantChain;

  protected boolean explicitlyNamed;

  protected boolean annotationsProcessed;

  /** This type's functionAspect, specifying the signature of functions this type represents. */
  public FunctionAspect functionAspect;
  
  /* Condition for being registered. */
  public Condition registered;
  
  /* Condition for this type being "prepared", meaning wired, hence fully initialized and ready for use. */
  public Condition prepared;
  
  // ======================================================================
  // Constructors and Initializers
  // ======================================================================
  static {
    for(Flag t : ILLEGAL_TYPE_TAGS)
      illegalTags.add(t);
  }

  // ======================================================================
  // Methods
  // ======================================================================
  // ---------------------------
  // Property Access
  // ---------------------------
  /**
   * Register the facet having <code>baseFacetName</code> under <code>alias</code>.
   */
  public Type<?> aliasFacetAs(String baseFacetName, String alias) {
    // Facet f = rawFacet(baseFacetName);
    // Assertion.check(f != null, "no facet named %s exists", baseFacetName);
    // Assertion.check(rawFacet(alias) == null, "alias %s already exists", alias);
    // attributes().put(alias, f);
    // return this;
    throw new Unfinished();
  }

  public ArrayType arrayType() {
    // the only way to create an array type from a ground type is to create an
    // instance and get its class
    Object array = Array.newInstance(iClass != null ? iClass : Object.class, 0);
    return (ArrayType) typeOf(array);
  }

  /**
   * Returns a traverser on this type's inheritance graph.
   */
  public TypeAncestryTraversal ancestryTraverser() {
    wireUp();
    TypeAncestryTraversal t = (TypeAncestryTraversal) platform_.models.typeAncestry.instance();
    t.wireUp();
    t.accept(this);
//    t.free();
    return t;
  }

  /**
   * Marshals all my annotations into <code>annoList</code>.
   */
  public List<Annotation> annotations() {
    UniqueOrderedAccumulator<Annotation> acc = new UniqueOrderedAccumulator();
    for(Annotation a : iClass.getAnnotations())
      acc.add(a);
    outEdges().forEach(e -> {
      Type ancestor = ((TypeInheritance) e).target();
      if(ancestor.isInterface())
        acc.addAll(ancestor.annotations());
    });
    return acc.accumulation();
  }

  /**
   * Returns this type if its an EntityType, else null.
   */
  public EntityType asEntityType() {
    return null;
  }

  /**
   * Returns this type's base type.
   */
  public Type<?> baseType() {
    return isBaseType() ? this : supertype().baseType();
  }

  /**
   * Returns the behaviorRegistry containing methods defined on the iClass.
   */
  public BehaviorRegistry behaviors() {
    if(behaviors == null) {
      if(isBaseType()) {
        // base types create their own map
        behaviors = new BehaviorRegistry(this);
      } else if(supertype() != null) {
        // variants just use their baseType's map
        behaviors = supertype.behaviors();
      }
    }
    return behaviors;
  }

  /**
   * Returns this type's containment, lazily creating it.
   */
  public ContainmentAspect containment() {
//    return isCollectionType() ? (ContainmentAspect) functionAspect() : null;
    return (ContainmentAspect) functionAspect();
  }

  /**
   * If the iClass is defined and has a declaring class, returns the declaring class's type, else
   * returns null.
   */
  public Type<?> declaringType() {
    if(iClass != null) {
      Class declaringClass = iClass.getDeclaringClass();
      return declaringClass != null ? types_.apply(declaringClass) : null;
    } else {
      return null;
    }
  }

  /**
   * Returns this type's digest.
   */
  // public String digest() {
  // return name;
  // }

  /**
   * Evaluates this type, treated as an expression, returning the equivalent type.
   */
  public Type eval() {
    return this;
  }

  // @Override
  public TypeExpression apply(ITypeScope scope) {
    throw new Unfinished();
  }

  /**
   * Returns whether the given object is an instance of this type.
   */
  public boolean contains(Object object) {
    return iClass != null && iClass.isInstance(object);
  }

  /**
   * Returns the default value for this type.
   */
  public Object defaultValue() {
    return null;
  }

  public String displayName() {
    return hasPid() ? primaryId().displayName() : iClass.getSimpleName();
  }

  /**
   * Returns this type's displayName.
   */
  public void displayName(String newName) {
    primaryId().displayName(newName);
  }

  /**
   * Returns this type's list of facets, listed in top-down inheritance order.
   */
  public FacetFlow<Facet> facets() {
    return new FacetFlow();
  }

  /**
   * Returns this type's list of facets, listed in top-down inheritance order.
   */
  public List<Facet> facetList() {
    return new ArrayList();
  }

  /**
   * Sets the format used by this type's translator.
   */
  public Type<?> format(Format format) {
    translator(new FormattingTranslator(this, format));
    return this;
  }

  /**
   * Returns this type's function aspect, or null if it has none.
   */
  public FunctionAspect functionAspect() {
    // if(iClass == EqualityMap.class && isBaseType())
    // armTrap("eqmap");
    if(functionAspect == null) {
      // force creating supertype
      if(supertype == null)
        supertype();

      // nothing to resolve if not parametric
      if(signature == null && (supertype == null || supertype.signature == null))
        return null;

      if(ECollection.class.isAssignableFrom(iClass)) {
        functionAspect = platform_.containments.containmentFor(iClass);
      } else {
        functionAspect = new FunctionAspect();
      }
      functionAspect.owner(this);
      
      // extract type params from class definition
      extractClassParameters();

      functionAspect.refineSignature(this);
    }
    return functionAspect;
  }

  /**
   * Returns a flow on this type's fields.
   */
  public FieldFlow fields() {
    throw new Unfinished();
  }

  /**
   * Returns this type's identityAspect. This method returns null since only entityTypes
   * have identity.
   */
  public IdentityAspect identity() {
    return null;
  }

  /**
   * Returns this type's injection points.
   */
  public List<Facet> injectionPoints() {
    throw new Unfinished();
  }

  /**
   * Returns this type's hashCode.
   */
  public int hashCode() {
    TypeAddress primaryId = primaryId();
    return primaryId != null ? primaryId().hashCode() : iClass.hashCode();
  }

  /**
   * Returns the field containing instances' hashCodes.
   */
  public Field hashcodeField() {
    throw new UnsupportedOperationException();
  }

  /**
   * Returns whether <code>object</code> is an instance of this type.
   */
  public boolean hasInstance(Object object) {
    return iClass.isInstance(object);
  }

  /**
   * Returns whether this type has a local facet having <code>name</code>.
   */
  public boolean hasLocalFacet(String name) {
    return false;
  }

  public boolean hasNumParams(int num) {
    return signature != null && num == signature.size();
  }

  /**
   * Returns whether this type's out exists and is <code>ot</code>.
   */
  public boolean hasOutType(Type ot) {
    Type vt = out();
    return vt != null && vt == ot;
  }

  /**
   * Returns whether this type has parameters having the respective <code>paramTypes</code>.
   */
  public boolean hasParameterTypes(Type[] paramTypes) {
    if(hasNumParams(paramTypes.length)) {
      IntFlow i = new IntFlow();
      for(Type t : paramTypes) {
        if(signature.apply(i.next()).valueType() != t)
          return false;
      }
      return true;
    } else {
      return false;
    }
  }

  /**
   * Returns whether this type has the base name <code>n</code>.
   */
  public boolean hasBaseName(String n) {
    return iClass.getSimpleName().equals(n);
  }
  
  /**
   * Returns whether this type specifies a member type.
   */
  public boolean hasValueType() {
    Type vt = out();
    return vt != null && !vt.isSpecified();
  }

  /**
   * Returns the class of this type's instances
   */
  public Class<T> iClass() {
    return iClass;
  }

  /**
   * Sets the class of this type's instances.
   */
  public void iClass(Class<T> ic) {
    iClass = ic;
    initMeta();
    if(isBaseType())
      initFlags();
  }

  /**
   * Returns this type's inner type named <code>innerTypeName</code>, or null.
   */
  public Type<?> innerType(Object innerTypeName) {
    return innerTypes().flow().select(t -> t.baseName().equals(innerTypeName));
  }

  /**
   * Returns this type's inner types, i.e. this types for member classes of this type's iClass.
   */
  public Sequence<Type> innerTypes() {
    Sequence<Type> innerTypes = new Sequence();
    try {
      if(iClass != null) {
        Class[] innerClasses = iClass.getDeclaredClasses();
        for(int i = 0; i < innerClasses.length; i++)
          innerTypes.add(types_.apply(innerClasses[i]));
      }
    } catch(TypeNotFoundException e) {
      println(this + ": error fetching inner classes (ignored)");
      e.printStackTrace();
    }
    return innerTypes;
  }

  public Metatype metatype() {
    if(metatype == null)
      metatype = platform_.metatypes.apply(iClass);
    return metatype;
  }

  /**
   * Returns whether this type represents a reference.
   */
  public StructureType<?> outerType() {
    if(iClass != null) {
      // if have a iClass, look for declaring class
      Class outerClass = iClass.getEnclosingClass();
      return outerClass != null ? types_.applyForStructureType(outerClass) : null;
    } else {
      // if no iClass, attempt to find via name analysis
      int dollarIndex = name.lastIndexOf('$');
      return dollarIndex > -1 ? types_.applyForStructureType(name.substring(0, dollarIndex)) : null;
    }
  }

  /**
   * Returns whether this type's instances have names.
   */
  public boolean instancesNamed() {
    return INamed.class.isAssignableFrom(iClass);
  }

  /**
   * Returns whether this is a function type, i.e. whether it has a functionAspect.
   */
  public boolean isFunctionType() {
    return functionAspect() != null;
  }

  /**
   * Returns this type's in. This method exists to unify Type and FunctionType.
   */
  public Type in() {
    return functionAspect().in();
  }

  /**
   * Returns whether this is an abstract type, describing an abstract class.
   */
  public boolean isAbstract() {
    if(iClass == null)
      return true;
    if(isArrayType())
      return Modifier.isAbstract(iClass.getComponentType().getModifiers());
    return iClass != null && Modifier.isAbstract(iClass.getModifiers());
  }

  /**
   * Returns whether this type is an alias.
   */
  public boolean isAlias() {
    return primaryId().isAlias();
  }

  /**
   * Returns whether this is anonymous.
   */
  public boolean isAnonymousType() {
    return iClass.isAnonymousClass();
  }

  public boolean isArrayType() {
    return false;
  }

  public boolean isAtom() {
    return meta().isAtom();
  }

  public boolean isBaseType() {
    TypeAddress primaryId = primaryId();
    return primaryId == null || primaryId.isBase();
  }

  /**
   * Returns whether this is a boolean type.
   */
  public boolean isBooleanType() {
    return metatype == net.ess.ebase.typeSystem.metatypes.Metatype.Boolean_;
  }

  /**
   * Returns whether this is an entity collection type.
   */
  public boolean isCollectionEntityType() {
    switch(metatype) {
      case CollectionEntity_:
      case Space_:
        return true;
      default:
        return false;
    }
  }

  public boolean isIterable() {
    return hasFlag(LIST);
  }

  /**
   * Returns whether this is a collection type.
   */
  public boolean isCollectionType() {
    return false;
  }

  /**
   * Returns whether this type describes entities.
   */
  public boolean isEntityType() {
    return false;
  }

  /**
   * Returns whether this is an enumerated type.
   */
  public boolean isEnum() {
    return iClass != null && iClass.isEnum();
  }

  public boolean isEqualityIdentity() {
    // setTripwire();
    Method m = methodFor("equals", Object.class);
    return false;
  }

  public boolean isEquivalentTo(Type t) {
    if(t.iClass != iClass)
      return false;
    if(primaryId().equals(t.primaryId()))
      return false;
    return true;
  }

  public boolean isExplicitlyNamed() {
    return explicitlyNamed;
  }

  /**
   * Returns whether this set is finite (aka <i>bounded</i>), i.e. has a finite extent.
   */
  public boolean isFinite() {
    return false;
  }

  /**
   * Returns whether this type represents functions.
   */
  public boolean isFunctional() {
    return Function.class.isAssignableFrom(iClass);
  }

  /**
   * Returns whether this type is an immediate subtype of type <code>t</code>, that is, t is one of
   * my ancestors.
   */
  public boolean isImmediateSubtypeOf(Type t) {
    Source<TypeInheritance> supers = outEdges().filter(TypeInheritance.class);
    for(TypeInheritance ti : supers) {
      if(ti.target == t)
        return true;
    }
    return false;
  }

  /**
   * Returns whether this type's instances are immutable.
   */
  public boolean isImmutable() {
    return hasFlag(IMMUTABLE);
  }

  @Override
  public boolean isInstantiable() {
    return hasFlag(INSTANTIABLE);
  }

  /**
   * Returns whether this type's s are t_integer values of various valueTypes.
   */
  public boolean isInteger() {
    return metatype.isInteger();
  }

  /**
   * Returns whether this type declares an interface, i.e. its iClass is an interface.
   */
  public boolean isInterface() {
    return iClass.isInterface();
  }

  /**
   * Returns whether this type is an inner type.
   */
  public boolean isInnerType() {
    return iClass.getEnclosingClass() != null;
  }

  /**
   * Returns whether this type defines lists.
   */
  public boolean isListType() {
    return List.class.isAssignableFrom(iClass);
  }

  /**
   * Returns whether this type defines maps.
   */
  public boolean isMapType() {
    return Map.class.isAssignableFrom(iClass);
  }

  /**
   * Returns whether this type is nested in an outer type.
   */
  public boolean isNested() {
    return iClass != null && iClass.getDeclaringClass() != null;
  }

  /**
   * Returns whether <code>value</code> is nullish, i.e. represents 
   * undefined, unsupplied, or no value.
   */
  public boolean isNullish(Object value) {
    return value == null;
  }

  /**
   * Returns whether this type's instances are numeric values.
   */
  public boolean isNumeric() {
    return metatype.isNumeric();
  }

  /**
   * Returns whether this is a structType.
   */
  public boolean isStructureType() {
    return false;
  }

  /**
   * Returns whether this type has parameters.
   */
  public boolean isParametric() {
    return signature() != null;
  }

  /**
   * Returns whether this type has parameters with specified types.
   */
  public boolean isSpecifiedParametric() {
    return signature() != null && signature.isSpecified();
  }

  /**
   * Returns whether this type is a subtype of a parameteric base type.
   */
  public boolean isSubtype() {
    return primaryId().kind().isSubtype();
  }

  public boolean isPartiallyOrderedType() {
    return false;
  }

  /**
   * Returns whether this type is primitive.
   */
  public boolean isPrimitive() {
    return false;
  }

  /**
   * Returns whether this is a placeholder type.
   */
  public boolean isPlaceholder() {
    return false;
  }

  /**
   * Returns whether this type's iClass is public.
   */
  public boolean isPublic() {
    return iClass != null && Modifier.isPublic(iClass.getModifiers());
  }

  /**
   * Returns whether this type's instances are real values.
   */
  public boolean isReal() {
    return metatype.isReal();
  }

  /**
   * Returns whether this type's instances are references.
   */
  public boolean isReferenceValued() {
    return false;
  }

  public boolean isSetType() {
    return false;
  }

  /**
   * Returns whether this is a space type.
   */
  public boolean isSpaceType() {
    switch(metatype) {
      case Space_:
      case Host_:
        // case Container_:
        return true;
      default:
        return false;
    }
  }

  /**
   * Returns whether this type is specified, i.e. has at least one specified type bound.
   */
  public boolean isSpecified() {
    return iClass != Object.class && iClass != Any.class;
  }

  /**
   * Returns whether this is an object type, describing objects having reference semantics, and
   * typically heterogeneous attributes.
   */
  public boolean isStructured() {
    return hasFlag(STRUCTURED);
  }

  /**
   * Returns whether this type is a subtype of type <code>t</code>, that is, whether all of this
   * type's instances are also instances of t.
   */
  public boolean isSubMetatypeOf(Type t) {
    // return compareWith((Type) t).isLE();
    throw new Unfinished();
  }

  /**
   * Returns whether this type is a subtype of type <code>t</code>, that is, whether all of this
   * type's instances are also instances of t.
   */
  public boolean isSubtypeOf(Type t) {
    if(t == this)
      return true;

    TypeComparisonKind tck = compareWith(t); // hacky patch
    if(tck == null)
      return false;
    boolean isSubtype = tck.isLE();
    // boolean isSubtype = t.iClass.isAssignableFrom(iClass);
    // boolean isSubtype = t.iClass.isAssignableFrom(iClass);
    return isSubtype;
  }

  public boolean isTaggedVariant() {
    throw new Unfinished();
  }

  /**
   * Returns whether this is a textType.
   */
  public boolean isTextType() {
    return false;
  }

  /**
   * Returns whether this type's iClass is static.
   */
  public boolean isStatic() {
    return iClass != null && Modifier.isStatic(iClass.getModifiers());
  }

  public boolean isTotallyOrdered() {
    return false;
  }

  /**
   * Returns whether this is a value type.
   */
  public boolean isValueType() {
    return false;
  }

  public TypeKind kind() {
    return primaryId().kind();
  }

  public Class normalizedValueClass() {
    return iClass;
  }

  public Type out() {
    return functionAspect().out();
  }

  /**
   * Returns this type of the parameter designated by <code>index</code>.
   */
  public Type<?> parameterType(int index) {
    if(signature != null) {
      TypeParameter p = signature.apply(index);
      return p.valueType();
    } else {
      return null;
    }
  }

  /**
   * Returns the sublist of persistable facets.
   */
  public List<Facet> persistableFacets() {
    ArrayList<Facet> pAtts = new ArrayList<Facet>();
    for(Facet att : attributes()) {
      if(att.isPersistable())
        pAtts.add(att);
    }
    return pAtts;
  }

  public boolean hasPid() {
    if(meta == null)
      return false;
    return meta.key != null;
  }

  /**
   * Returns a flow over the facets defined by this source.
   */
  public FacetFlow<Facet> localFacets() {
    return new FacetFlow(this);
  }

  @Override
  public TypeAddress primaryId() {
    return (TypeAddress) meta().key();
  }

  /**
   * Sets this type's primaryId to (the value of) {@link address}. [then binds this type to address]?
   */
  public void primaryId(TypeAddress address) {
    if(address != meta().key) {
      meta.key(address);
      name(address.name);
      iClass(address.iClass);
      
      // check for null address signature
      boolean hasSig = signature != null;
      signature = address.signature;
      if(iClass == EqualityMap.class && isBaseType())
        armTrap("eqmap");
      if(signature == null && hasSig)
        trap = 2;
    }
  }

  /**
   * If this is an entity type, returns the attribute carrying instance entities' unique identities,
   * else returns null.
   */
  public Facet primaryIdFacet() {
    throw new UnsupportedOperationException("identity");
  }

  /**
   * Returns the iClass, or its primitive equivalent if a wrapper class.
   */
  public Class primitiveClass() {
    return iClass;
  }

  /**
   * Returns the designated facet. If one isn't found, attempts to create a behavioral facet.
   * Returns null if <code>facetName == null</code>.
   */
  public Facet rawFacet(String facetName) {
    return facetName == null ? null : attribute(facetName);
  }

  /**
   * Renames this entity to <code>newName</code>.
   */
  public Type name(String newName) {
    String oldName = name;
    super.name(newName);

    // if this is a rename, propagate to primaryId and container
    if(oldName != null) {
      TypeAddress addr = primaryId();
      addr.name(newName);
      Space container = space();
      if(container != null)
        container.keyUpdated(this, oldName, newName);
    }
    return this;
  }

  /**
   * Returns this type's baseName.
   */
  public String baseName() {
    if(hasPid()) {
      return primaryId().baseName();
    } else {
      return iClass.getSimpleName();
    }
  }

  /**
   * Returns this type's base supertype, skipping over subtypes.
   */
  public Type<?> baseSupertype() {
    Type bst = supertype();
    while(bst.isSubtype())
      bst = bst.supertype();
    return bst;
  }

  /**
   * Returns this type's immediate subtypes.
   */
  public IdentitySet<Type> localSubtypes() {
    Source<TypeInheritance> f = inEdges().filter(TypeInheritance.class);
    return f.map(i -> i.source).toSet();
  }

  /**
   * Returns the subtype closure under this type.
   */
  public IdentitySet<Type> allSubtypes() {
    if(allSubtypes == null) {
      allSubtypes = new IdentitySet();
      try(
        ScanResult scanResult = 
          new ClassGraph()
            .enableAllInfo()
            .acceptPackages("net.ess").scan()) {
              ClassInfoList controlClasses = scanResult.getSubclasses(iClass);
              controlClasses.loadClasses().forEach(c -> allSubtypes.add(types_.apply(c)));
          };
    }
    return allSubtypes;
  }

  public TypeParameterSignature signature() {
    if(signature == null) {
      signature = primaryId().signature();
      
      if(signature != null) 
        Assertion.check(functionAspect == null);
    }
    return signature;
  }

  /**
   * Returns this type's structure aspect.
   */
  public StructureAspect structure() {
    return emptyStructure;
  }

  /**
   * Returns this type's supertype, lazily initializing it.
   */
  public Type<?> supertype() {
    // bind supertype if null and there's a superclass
    if(supertype == null) {
      Type ancestor = null;
      switch(kind()) {
        case baseType:
          Class sc = iClass.getSuperclass();
          if(sc != null)
            ancestor = types_.apply(sc);
          break;
        case subtype:
        case aliasType:
          ancestor = types_.apply(iClass);
          Assertion.check(ancestor != this);
      }
      if(ancestor != null)
        addAncestor(ancestor);
    }
    return supertype;
  }

  /**
   * Returns the label of flags referring to this type.
   */
  public String tagName() {
    return uncapitalize(baseName());
  }

  public IValueTranslator translator() {
    if(translator == null)
      initTranslator();
    return translator;
  }

  public void translator(IValueTranslator newTranslator) {
    // if(translator != null && translator != newTranslator) {
    // traceAlways("WARNING: replacing existing translator %s with %s", translator, newTranslator);
    // new Throwable().printStackTrace();
    // }
    translator = newTranslator;
  }

  /**
   * Returns a record type providing a columnar view of this type.
   */
  public TupleType tupleType() {
    return new TupleType(this);
  }

  /**
   * Returns the package containing the iClass.
   */
  public TypePackage typePackage() {
//    return platform_.packages.getPackage(name);
    throw new Unfinished();
  }

  /**
   * Returns this typeSystem's typeStats.
   */
  public TypeStats typeStats() {
    return platform_.typeSystem.typeStats();
  }

  /**
   * Returns the inheritance from this type up to <code>supertype</code>.
   */
  public TypeInheritance upTo(Type supertype) {
    // FIX ME: Unsafe: edge could be bindingFlavor!
    return (TypeInheritance) findEdgeTo(supertype);
  }

  // ---------------------------
  // TypeParameter Access
  // ---------------------------
  /**
   * Returns the parameter having <code>name</code> whose value references this type, lazily
   * creating it.
   */
  public synchronized TypeParameter inboundParameter(String name) {
    if(inboundParameters == null)
      inboundParameters = new HashMap();
    TypeParameter p = inboundParameters.get(name);
    if(p == null) {
      p = new TypeParameter(name, this);
      inboundParameters.put(name, p);
    }
    return p;
  }

  // ---------------------------
  // Comparison and Hashing
  // ---------------------------
  @Override
  protected void computeHashCode() {
    hash(primaryId());
  }

  // ---------------------------
  // Lifecycle Management
  // ---------------------------
  /**
   * Adds <code>ancestor</code> as a supertype of this type, registering the first ancestor as this
   * type's supertype. Returns the resulting new inheritance, or null if already exists.
   */
  public synchronized TypeInheritance addAncestor(Type ancestor) {
    TypeInheritance inheritance = new TypeInheritance(this, ancestor);
    inheritanceAdded(inheritance);
    return inheritance;
  }

  /*
   * Attaches <code>builder</code> and its handle.
   */
  public void attachBuilder(TypeBuilder builder) {
    this.builder = builder;
    iClass = builder.iClass;

    // check pids
    TypeAddress typesPid = primaryId();
    TypeAddress builderPid = builder.address();
    if(typesPid == null)
      primaryId(builderPid);
    metatype = builder.metatype();
    registered = typesPid.registered;
  }

  @Override
  public void becomeTemplate() {}

  /**
   * Returns this type's builder, lazily creating it.
   */
  public TypeBuilder builder() {
    if(builder == null)
      builder = new TypeBuilder(this);
    return builder;
  }

  @Override
  public void finishCloning() {
    TypeAddress pidClone = (TypeAddress) primaryId().clone();
    super.finishCloning();
    meta.key(pidClone);
    allSubtypes = null;
    annotationsProcessed = false;
    builder = null;
    explicitlyNamed = false;
    extent = null;
    functionAspect = null;
    inboundParameters = null;
    prepared = null;
    registered = null;
    signature = null;
    supertype = null;
    variantChain = null;
  }

  @Override
  public void initBuilder(EntityBuilder b) {
    super.initBuilder(b);
    builder = (TypeBuilder) b;
  }

  private void initFlags() {
    metatype();

    // bail on Any_
    if(metatype == Any_)
      return;

    int clone = 0;
    int dontClone = 0;

    if(Function.class.isAssignableFrom(iClass))
      plus(FUNCTION);

    if(metatype.isImmutable()) {
      plus(IMMUTABLE);
      dontClone++;
    }

    if(metatype.isAtom()) {
      plus(ATOM);
      dontClone++;
    }

    if(metatype.isA(Reference_)) {
      plus(REFERENCE_VALUED);
    }

    if(metatype.structured) {
      if(iClass == Class.class)
        trap = 2;
      plus(STRUCTURED);
      minus(ATOM);
    }

    if(iClass.isArray()) {
      plus(ARRAY);
    }

    if(ECollection.class.isAssignableFrom(iClass)) {
      plus(ECOLLECTION);
    }

    if(Collection.class.isAssignableFrom(iClass) && !hasFlag(ECOLLECTION)) {
      plus(JCOLLECTION);
    }

    if(List.class.isAssignableFrom(iClass)) {
      plus(LIST);
    }

    if(Map.class.isAssignableFrom(iClass)) {
      plus(MAP);
    }

    if(EObject.class.isAssignableFrom(iClass)) {
      plus(EOBJECT);
    }

    if(IStructure.class.isAssignableFrom(iClass) && !iClass.isInterface()) {
      plus(STRUCTURE);
      if(dontClone > 0) {
        System.err.println("conflict");
      }
      clone++;
    }

    if(Entity.class.isAssignableFrom(iClass)) {
      plus(ENTITY);
    }

    if(Graph.class.isAssignableFrom(iClass)) {
      plus(GRAPH);
    }

    if(Node.class.isAssignableFrom(iClass)) {
      plus(NODE);
    }

    if(metatype == Connective_) {
      plus(CONNECTIVE);
    }

    if(GraphElementGroup.class.isAssignableFrom(iClass)) {
      plus(GROUP);
    }

    if(Component.class.isAssignableFrom(iClass)) {
      plus(COMPONENT);
    }

    if(dontClone > 0) {
      if(clone > 0) {
        throw new AbortException("%s has CLONEABLE conflict", this);
      } else {
        // noop
      }
    } else {
      // unless marked uncloneable, and extends Cloneable, then clone
      if(Cloneable.class.isAssignableFrom(iClass))
        clone++;

      // ditto instantiable
      if(ReflectionUtils.isTypeInstantiable(null, iClass)) {
        plus(INSTANTIABLE);
        clone++;
      }

      if(clone > 0) {
        plus(CLONEABLE);
      } else {
        // noop
      }
    }

    // check invariants
    // ATOM.checkMutuallyExclusive(OBJECT);
    JCOLLECTION.checkMutuallyExclusive(ECOLLECTION);

    // TEMP disabled
    // Assertion.check(!Edge.class.isAssignableFrom(iClass) && hasTag(CONNECTIVE));
    // Assertion.check(!IBinding.class.isAssignableFrom(iClass) && hasTag(CONNECTIVE));

//    if(ReflectionUtils.isClassInJdk(iClass)) {
//      plus(OPAQUE);
//      println("%s is opaque", this);
//    }
//
//    if(iClass == HashMap.class)
//      trap = 2;
    
    // show();

  }

  public void plus(Flag... flags) {
    meta().plus(flags);
    if(iClass == LifecycleState.class) {
      Flag t0 = flags[0];
      if(illegalTags.contains(t0)) {
        println("%s shouldn't contain flag %s", this, t0);
      }
    }
  }

  @Override
  public void initMeta() {
    if(iClass == EntityType.class)
      meta.entityType((EntityType) this);
    if(iClass != null)
      super.initMeta();
  }

  /**
   * Initializes this type's transform.
   */
  public void initTranslator() {
    if(translator == null) {
      translator = 
          isSubtype() 
            ? supertype.translator() 
            : TranslatorRegistry.instance.apply(this);
    }
  }

  /**
   * Injects all annotations on this type into <code>target</code>.
   */
  public void injectAnnotationsInto(ITypeAspect target) {
    registered.whenOccurs(platform_.annotations, "injectAlongPath", this, target);
  }

  /*
   * Marshals all my annotations into <code>annoList</code>.
   */
  public void marshalAnnotations(List<Annotation> annoList) {
    for(Annotation a : iClass.getAnnotations()) {
      annoList.add(a);
    }
    successorFlow().forEach(t -> ((Type)t).marshalAnnotations(annoList));
  }
  
  public LifecycleStateCondition onState(LifecycleState target) {
    throw new Unfinished();
  }
  
  /**
   * Returns the condition for this type being "prepared", hence fully 
   * initialized and ready for use. 
   */
  public Condition prepared() {
//    int depth = callStackDepth();
//    if(depth > 250)
//      trap = 2;
    if(prepared == null) {
//      prepared = new Condition(displayName() + ".prepared");
      prepared = new Condition();
    }
    return prepared;
  }

  // ---------------------------
  // Lifecycle Management
  // ---------------------------
  @Override
  public void doInitAction() {
    super.doInitAction();
    aspects = new TypeAspectSet();
  }

  @Override
  public void doSketchingAction() {
    if(supertype != null)
      supertype.sketch();
    super.doSketchingAction();
    typeStats().sketchedTypes++;
  }

  @Override
  public void doWiringAction() {
    if(supertype != null)
      supertype.wireUp();
    super.doWiringAction();
    functionAspect();
    typeStats().wiredTypes++;
  }

  /*
   * If iClass has a parametric superclass, extract types from its params and bind to my type params.
   */
  private void extractClassParameters() {
    TypeParameterSignature supersignature = null;
    ParameterizedType psc = null;
    java.lang.reflect.Type genericSuperclass = null;
    if(supertype != null && (supersignature = supertype.signature()) != null
        && (genericSuperclass = iClass
            .getGenericSuperclass()) instanceof ParameterizedType) {
      psc = (ParameterizedType) genericSuperclass;
      java.lang.reflect.Type[] args = psc.getActualTypeArguments();
      int nargs = args.length;
      for(int i = 0; i < nargs; i++) {
        java.lang.reflect.Type tArg = args[i];
        if(tArg instanceof TypeVariable) {
          TypeVariable v = (TypeVariable) tArg;
          String argName = v.getName();
          java.lang.reflect.Type[] bounds = v.getBounds();
          java.lang.reflect.Type bound = bounds[0];
          if(bound == Object.class)
            continue;
          Type newVT = types_.apply(bound);
          TypeParameter tp = signature.apply(argName);
          tp.refineValueType(newVT);
        }
      }
    }
  }

  /*
   * Finishes building this subtype of <code>supertype</code>, having <code>name</code> and
   * <code>componentType</code>.
   */
  protected synchronized void finishSubtype(Type supertype, String name) {
    addAncestor(supertype);
    initMeta();
    primaryId().kind(TypeKind.subtype);
    primaryId().name(name);
    Assertion.check(isSubtype());
    typeStats().subtypes++;
  }

  /**
   * Creates, attaches, and returns a new metaEntity.
   */
  public synchronized TypeLink newMeta() {
    return new TypeLink(this);
  }

  /*
   * Creates, attaches, and returns a new metaEntity.
   */
  public synchronized TypeLink newMeta(EntityType t) {
    Assertion.check(meta == null);
    return new TypeLink(this, t);
  }

  protected void updateTags(long delta) {
    boolean clearing = delta < 0;
    localSubtypes().forEach(t -> updateTags(delta));
  }

  // ---------------------------
  // Aspect Management
  // ---------------------------
  public TypeAspectSet aspects() {
    return aspects;
  }

  /**
   * Adds and returns a new aspect of type <code>A</code>.
   */
  public <A extends ITypeAspect> A addAspect(Class<A> aspectClass) {
    return addAspect(newInstance(aspectClass));
  }

  /**
   * Adds <code>aspect</code> of type <code>A</code>, returning the aspect. 
   */
  public synchronized <T extends ITypeAspect> T addAspect(T aspect) {
    quietlyAddAspect(aspect);
    return aspect;
  }

  /**
   * Return this thing's aspect having <code>aspectClass</code>, lazily creating it.
   */
  public <T extends ITypeAspect> T getAspect(Class<T> aspectClass) {
    T aspect = peekAspect(aspectClass);
    if(aspect == null) {
      aspect = addAspect(newInstance(aspectClass));
      if(aspect.owner() == null)
        aspect.owner(this);
    }
    return aspect;
  }

  /**
   * Returns whether this type has any aspect instance of <code>aspectClass</code>.
   */
  public boolean hasAspect(Class aspectClass) {
    return aspects.hasAspect(aspectClass);
  }

  /**
   * Return this thing's aspect having <code>aspectClass</code>, or null if it has no such aspect.
   */
  public <T extends ITypeAspect> T peekAspect(Class<T> aspectClass) {
    return aspects.apply(aspectClass);
  }

  /**
   * Adds <code>aspect</code>. If another aspect of the same class is already in aspects, and this
   * type shares aspects with its supertype, clones aspects and replaces the existing aspect with
   * <code>aspect</code>.
   */
  public synchronized void quietlyAddAspect(ITypeAspect aspect) {
    ITypeAspect existing = aspects.apply(aspect.getClass());
    if(existing != aspect)
      aspects.add(aspect);
  }

  // ---------------------------
  // Instantiation
  // ---------------------------
  /**
   * Creates a new instance of this type.
   */
  public T instance() {
    if(isAbstract())
      throw new AbortException("attempting to instantiate an abstract type: %s", name);

    if(IFyle.class.isAssignableFrom(iClass))
      return newInstance(iClass);

    Class enclosing = iClass.getEnclosingClass();
    if(enclosing != null) {
      try {
        Constructor<T> cons = iClass.getConstructor(new Class[] {enclosing});
        return cons.newInstance(new Object[] {null});
      } catch(Exception e) {
        e.printStackTrace();
        return null;
      }
    } else {
      return newInstance(iClass);
    }
  }

  /**
   * Creates and returns a new instance of the submodel indicated by <code>subModelSelector</code>.
   */
  public T newInstance(Object subModelSelector) {
    throw new AbortException(
        "Qualified instantiation not supported by this model, " + "consider using newInstance()");
  }

  /**
   * Creates an instance of this type that's contained in <code>outer</code>.
   */
  public T newInnerInstance(Object outer) {
    try {
      T instance = instance();
      Field f = iClass.getDeclaredField("this$0");
      f.setAccessible(true);
      f.set(instance, outer);
      return instance;
    } catch(Exception e1) {
      dispatchException(e1);
      return null;
    }
  }

  // ---------------------------
  // Subtype Access
  // ---------------------------
  /**
   * Returns the subtype having instances of <code>oType</code>, in effect narrowing the out.
   */
  public Type<?> subtypeHavingOutType(Type oType) {
    return (Type<?>) new SubtypeBuilder(this).out(oType).build();
  }

  /**
   * Returns the parametric subtype of this type having parameters with values =
   * <code>paramTypes</code>, and names = parallel signature.
   */
  public Type<T> subtypeHavingParamTypes(Type[] paramTypes) {
    return new SubtypeBuilder(this).paramTypes(paramTypes).build();
  }

  // ---------------------------
  // Aspect Management
  // ---------------------------
  /**
   * Appends <code>subtype</code> to the variants chain.
   */
  void addVariant(Type subtype) {
    Assertion.check(isBaseType() && !subtype.isBaseType());
    subtype.variantChain = variantChain;
    variantChain = subtype;
  }

  /**
   * Returns this thing's aspect instance of <code>aspectClass</code>, bound to the facet
   * designatged <code>facetName</code>, creating the aspect if unbound.
   */
  public ITypeAspect fetchAspect(String facetName, Class<ITypeAspect> aspectClass) {
    if(aspects == null)
      return null;
    ITypeAspect a = aspects.apply(aspectClass);
    if(a == null)
      a = (ITypeAspect) facetValue(facetName);
    return a;
  }

  // ---------------------------
  // Event Handling
  // ---------------------------
  /**
   * Handles occurrence of the addition of <code>inheritanceEdge</code>.
   */
  public void inheritanceAdded(TypeInheritance inheritanceEdge) {
    Type ancestor = inheritanceEdge.target;
    if(supertype == null) {
      Assertion.check(ancestor != this);        // check not self
      Assertion.check(functionAspect == null);  // verify that functionAspect unbound
      supertype = ancestor;
    }

    // inherit flags
    meta().inherit(supertype.meta());
  }

  /**
   * Receives notification that <code>facet</code> has been discovered as a member of this type.
   */
  public void facetDiscovered(Facet facet) {}

  // ---------------------------
  // Extent Management
  // ---------------------------
  /**
   * Adds <code>subextent</code>.
   */
  public synchronized void addSubextent(TypeExtent subextent) {
    if(extent != null && !isFinite())
      extent.addSubextent(subextent);
  }

  /**
   * Binds <code>newExtent</code> to this type as it's extent, returning immediately if already
   * bound. This binding action is then recursed to subtypes. When this type already has an extent,
   * it instead attaches <code>newExtent</code> as the extent's parent.
   */
  public void bindExtent(TypeExtent newExtent) {
    extent = newExtent;

    if(entityRegistry() != null) {
      synchronized(entityRegistry()) {
        // add all instances to extent if this is an entity type
        // THIS MAY BE A NO-OP, since this method should be called before instantiating
        if(isEntityType())
          entityRegistry().flow().filter((Class<IEntity>) iClass).pumpTo(extent);

        // if the supertype is finite, add my extent to its extent
        supertype.addSubextent(extent);

        // erase nullExtents on subtypes to reflect that a supertype extent now exists
        // TypeAncestryWalker subtypes = ancestryWalker().down();
        // subtypes.forEach(subtype -> {
        // if(subtype.extent == nullExtent())
        // subtype.extent = null;
        // });
      }
    }
  }

  /**
   * If this is an entity type, returns a dataView of this type's registered instances, i.e. a view
   * containing the registered entity instances of this type and its subtypes. This method creates
   * the extent if it doesn't already exist. If this isn't an entity type, returns null.
   */
  public TypeExtent<T> extent() {
    if(extent == null) {
      wireUp();
      if(extent == null)
        bindExtent(new StrongTypeExtent(this));
    }
    return extent;
  }

  /**
   * Returns this type's extent, failing if has none.
   */
  public TypeExtent<T> extentOrFail() throws UnknownSetExtentException {
    if(extent == null)
      throw new UnknownSetExtentException("%s: attempting to fetch null extent", this);
    return extent;
  }

  /**
   * If this is an entity type, returns this type's extent, or if it doesn't have an extent of its
   * own, then the extent of the nearest supertype having an extent. Returns <tt>null</tt> if no
   * extent is bound in this type's entity type ancestry, or this isn't an entity type. As an
   * optimization, resolves the extent inheritance the first time this is called.
   */
  public synchronized TypeExtent enclosingExtent() {
    if(extent == null && isEntityType()) {
      TypeExtent te = null;
      for(Type t = supertype(); t instanceof StructureType; t = t.supertype()) {
        te = ((StructureType) t).extent;
        if(te != null) {
          extent = te;
          break;
        }
      }

      // if no extent found, bind a nullExtent to bypass the ancestor
      // search on subsequent calls
      if(extent == null)
        extent = nullExtent();
    }
    return extent != nullExtent ? extent : null;
  }

  /**
   * Returns whether this tyep has an extent.
   */
  public boolean hasExtent() {
    return extent != null;
  }

  /*
   * Returns a nullExtent, lazily creating it.
   */
  protected static TypeExtent nullExtent() {
    if(nullExtent == null) {
      nullExtent = new StrongTypeExtent();
      nullExtent.out(types_.entity_);
    }
    return nullExtent;
  }

  /**
   * Adds <code>instance</code> to extent if bound.
   */
  public void registerInstance(T instance) {
    if(extent != null)
      extent.add(instance);
  }

  /**
   * Removes <code>instance</code> from extent if bound.
   */
  public void unregisterInstance(T instance) {
    if(extent != null)
      extent.remove(instance);
  }

  // ---------------------------
  // Type Parameter Access
  // ---------------------------
  /**
   * Returns this type's type parameter that's designated by <code>id</code>.
   */
  public TypeParameter parameter(Identifier id) {
    return signature() != null ? signature.apply(id) : null;
  }

  /**
   * Returns the parameter that's designated by <code>targetId</code>, or has an ancestor so designated.
   */
  public TypeParameter parameterFlowingTo(Identifier targetId) {
    TypeParameter u = parameter(targetId);
    if(u != null) {
//      println("%s: paramFlowingTo(%s) = %s", this, targetId, u);
      return u;
    }

    if(iClass == EqualityMap.class && isBaseType() && targetId.name == "Out")
      armTrap("eqmap");
    
    if(!isParametric())
      return supertype != null ? supertype.parameterFlowingTo(targetId) : null;

    // since parameter no found on this type, try for path to target from each parameter, q
    for(TypeParameter q : signature) {
      Identifier pId = q.id; // name of param at current point in chain
      TypeParameter formal, actual, p = q;

      // walk up ancestry, following chain from actuals to formals
      for(Type tt = this; tt != null; tt = tt.supertype()) {
        // got a match, return it
        if(pId == targetId) {
//          println("%s.%s flows to %s.%s, returning %s", this, p, p.owner(), targetId, q);
          return q;
        }
        
        // no params, bail
        if(!tt.isParametric())
          return null;
        
        formal = tt.parameter(pId);
        actual = tt.signature().getParamWithActual(pId);
//        println(
//            "%s: target %s, pId %s, formal %s, actual %s", 
//            tt, targetId, pId, formal, actual);
        if(actual != null) {
          u = actual;
        } else if(formal != null) {
          u = formal;
        } else {
          return null;
        }
        pId = u.id;
      }
    }
    return null;
  }

  /**
   * Returns this type of the parameter designated by <code>parameterId</code>.
   */
  public Type<?> parameterType(Identifier parameterId) {
    TypeParameter p = parameter(parameterId);
    return p != null ? p.valueType() : types_.object_;  // if p not set, return object_t
  }

  // ---------------------------
  // Lattice Algebra
  // ---------------------------
  /**
   * Returns the kind of comparison this type has with type <code>t</code>.
   */
  public TypeComparisonKind compareInnerWith(Type other) {
    // if lifecycles are on, create and run traversers on both types' ancestors
    if(platform_.lifecycles.lifecycleManagerOnline.hasOccurred()) {
      Type p = this, q = other;
      TypeAncestryTraversal a0 = ancestryTraverser();
      a0.name("a0");
      TypeAncestryTraversal a1 = other.ancestryTraverser();
      a1.name("a1");

      // create intersection sets for each traverser
      IncrementalSet s0 = new IncrementalSet(a0);
      s0.name = "s0";
      IncrementalSet s1 = new IncrementalSet(a1);
      s1.name = "s1";
      
      // get the intersection, if any
      IntersectionSet<Type> is = new IntersectionSet(s0, s1);
      Type min = is.firstIntersection();
      // traceAlways(".min(%s) -> %s", other, min);
      
      // if intersection is at top of lattice, types were incomparable
      if(min == null ||min == types_.object_)
        return INCOMPARABLE;
      if(min == other)
        return SUB;
      if(min == this)
        return SUPER;

      // otherwise, 
      try {
        for(;;) {
          if(a0.get() == other)
            return SUB;
          if(a1.get() == this)
            return SUPER;
        }
      } catch(EndOfFlowException e) {
        return INCOMPARABLE;
      }
    } 
    
    // otherwise, since lifecycle manager is offline, just use simple class comparison
    else {
      if(other == this) 
        return EQUAL;
      if(other == null)
        return INCOMPARABLE;
      if(other.iClass.isAssignableFrom(iClass))
        return SUB;
      if(iClass.isAssignableFrom(other.iClass))
        return SUPER;
      return INCOMPARABLE;
    }
  }

  /**
   * Returns the kind of comparison this type has with type <code>t</code>.
   */
  public TypeComparisonKind compareWith(Type t) {
    // if share same iClass, compare for subtypeness
    if(t.iClass == iClass) {
      if(isSubtype()) {
        if(t.isSubtype()) {
          return SUB;
        } else {
          return SUB;
        }
      } else {
        if(t.isSubtype()) {
          return SUPER;
        } else {
          return EQUAL;
        }
      }
    } else {
      return comparisonWith(t).kind;
    }
  }

  /**
   * Returns the comparison this type has with type <code>t</code>.
   */
  public TypeComparison comparisonWith(Type t) {
    if(typeComparator == null)
      typeComparator = new TypeComparator();
    return typeComparator.compare(this, t);
  }

  /**
   * Returns the greatest lower bound (aka "infimum" or "meet" in lattice theory) of this and the
   * given type <code>t</code>, which is the most general type that is a subtype of both this and t.
   */
  public Type<?> glb(Type t) {
    if(t == null)
      return this;
    switch(compareWith(t)) {
      case EQUAL:
      case SUB:
        return this;
      case SUPER:
        return t;
      default: // case INCOMPARABLE:
        return types_.object_;
    }
  }

  /**
   * Returns whether this type is "less-than" <code>t</code>, i.e. is a descendant.
   */
  public boolean lt(Type t) {
    return compareWith(t) == SUB;
  }

  /**
   * Returns the lub ("least upper bound", aka "supremum" or "join" in lattice theory) of this and
   * the given type <code>t</code>, the most specific type of which both this and t are subtypes.
   */
  public Type<?> lub(Type t) {
    throw new Unfinished();
  }

  /**
   * Returns this type or <code>t</code> that's furthest from _Any, or the more specific type.
   */
  public Type min(Type t) {
    if(t == null || t == this)
      return this;
    if(!t.isSpecified())
      return this;
    if(!isSpecified())
      return t;
    if(t.iClass == Void.class)
      return this;
    switch(compareWith(t)) {
      case EQUAL:
        // case SUPER:
        // return this;
        // case SUB:
        // return t;
      case SUB:
        return this;
      case SUPER:
        return t;
      default: // case INCOMPARABLE:
        return types_.object_;
    }
    // IncrementalSet s0 = new IncrementalSet(directAncestry(), this);
    // IncrementalSet s1 = new IncrementalSet(other.directAncestry(), other);
    // IntersectionSet<Type> is = new IntersectionSet(s0,s1);
    // if(isArmed("props2"))
    // typeTrap = true;
    // Type min = is.firstIntersection();
    // traceAlways(".min(%s) -> %s", other, min);
    // return min;
  }

  /**
   * Returns this type or <code>t</code> that's closest to _Any, or less specific.
   */
  public Type max(Type t) {
    switch(compareWith(t)) {
      case SUPER:
        return this;
      default:
        return t;
    }
  }

  // ---------------------------
  // Facet Access
  // ---------------------------
  /**
   * Returns this type's designated facet.
   *
   * @throws IllegalArgumentException if no such facet exists
   */
  public Attribute attribute(String attributeName) {
    throw new TypeUnstructuredException(this);
  }

  /**
   * Returns this type's list of attributes, listed in top-down inheritance order.
   */
  public AttributeFlow attributes() {
    throw new TypeUnstructuredException(this);
  }

  /**
   * Returns this type's designated facet.
   */
  public Facet facet(String facetName) {
    throw new TypeUnstructuredException(this);
  }

  // ---------------------------
  // Behavior Access
  // ---------------------------
  /**
   * Returns the behavior having <code>methodName</code> and mapping on the given
   * <code>argClasses</code>. If a simple arg class match fails, expands the match to consider
   * behaviors having a final vararg. If no such behavior is found, throws a
   * MethodNotFoundException.
   */
  public Behavior behavior(String methodName, Class... argClasses) {
    return behaviorFinder(methodName).behavior(argClasses);
  }

  /**
   * Returns the behavior having <code>methodName</code> and mapping on the given <code>args</code>.
   * If a simple arg class match fails, expands the match to consider behaviors having a final
   * vararg. If no such behavior is found, throws a MethodNotFoundException.
   */
  public Behavior behavior(String methodName, Object... args) {
    return behaviorFinder(methodName).behavior(args);
  }

  /**
   * Creates and returns a behaviorFinder on this type.
   */
  protected BehaviorFinder finder() {
    return new BehaviorFinder(this);
  }

  /**
   * Creates and returns a behaviorFinder on this type, focused on <code>behaviorName</code>.
   */
  public BehaviorFinder behaviorFinder(String behaviorName) {
    return finder().name(behaviorName);
  }

  // ---------------------------
  // Method Access
  // ---------------------------
  /**
   * Returns the nullary method designated by <code>methodName</code>.
   */
  public Method method(String methodName) {
    return behaviorFinder(methodName).method();
  }

  /**
   * Returns the method designated by <code>methodName</code> taking the given
   * <code>argClasses</code>.
   */
  public Method methodFor(String methodName, Class... argClasses) {
    return behaviorFinder(methodName).method(argClasses);
  }

  /**
   * Returns the method having <code>methodName</code> and accepting <code>args</code>. If a simple
   * arg class match fails, expands the match to consider methods having a final vararg.
   */
  public Method methodFor(String methodName, Object... args) {
    return behaviorFinder(methodName).method(args);
  }

  /**
   * Returns the method having <code>buid</code>.
   */
  public Method methodFor(long buid) {
    return finder().method(buid);
  }

  /**
   * Returns the nullary method designated by <code>methodName</code>.
   */
  public Method methodNamed(String methodName) {
    return behaviorFinder(methodName).forAnyArgs().method();
  }

  // ---------------------------
  // Buid Access
  // ---------------------------
  /**
   * Returns the buid for <code>method</code>.
   */
  public long buidFor(Method method) {
    return finder().buid();
  }

  /**
   * Returns the buid for the method having the given <code>designator</code>.
   */
  public long buidFor(String designator) {
    // return findBehavior().designator(designator).buid();
    throw new Unfinished();
  }

  // ---------------------------
  // Command Access
  // ---------------------------
  /**
   * Adds the given command to the command list, replacing any synonymous command, else appending
   * the command to the list.
   */
  public synchronized void bindCommand(Command command) {
    behaviors().bindCommand(command);
  }

  /**
   * Returns the command with the given method name.
   */
  public Command command(String methodName) {
    return behaviors().command(methodName + "()");
  }

  // ---------------------------
  // Type Topology
  // ---------------------------
  /**
   * Returns the composite types that this type references, restricting them to just those
   * referenced via persistable attributes if <code>persistable</code> is <tt>true</tt>.
   */
  public IdentitySet<Type> getReferencedStructuredTypes(boolean persistable) {
    IdentitySet<Type> referencedTypes = new IdentitySet();
    for(Attribute attribute : attributes()) {
      if(persistable && !attribute.isPersistable())
        continue;
      Type valueType = attribute.out();
      if(valueType.isStructured())
        referencedTypes.add(valueType);
    }
    return referencedTypes;
  }

  // ---------------------------
  // Type Conversion
  // ---------------------------
  /**
   * Returns whether a widening conversion of instances of class <code>c</code> to this type's
   * iClass is legal (and will be applied by the VM).
   */
  public boolean allowsWideningConversionFrom(Class<?> c) {
    return iClass.isAssignableFrom(c);
  }

  /**
   * Returns whether a widening conversion of instances of class <code>c</code> to this type's
   * iClass is legal (and will be applied by the VM).
   */
  public boolean allowsWideningConversionFrom(Type t) {
    return allowsWideningConversionFrom(t.iClass);
  }

  /**
   * Returns <code>value</code>, coerced into this type's extent in an unconditional, primitive
   * fashion.
   */
  public Serializable coercePrimitively(Serializable value) {
    throw new UnsupportedOperationException();
  }

  // ---------------------------
  // Metaevaluation
  // ---------------------------
  public void apply(MetaInterpreter mi) {
    trap();
  }

  // ---------------------------
  // Semantic Processing
  // ---------------------------
  /**
   * Returns the expression resulting from applying <code>subst</code> to this expression.
   */
  public Type doSubstitution(TypeParameterSignature subst) {
    throw new Unfinished();
  }

  // ---------------------------
  // Transport Hooks
  // ---------------------------
  @Override
  public Object decode(String encoding) {
    throw new Unfinished();
    // return null;
  }

  // @Override
  // public Object decode(String encoding, ISpace dataSource) {
  // throw new Unfinished();
  // return null;
  // }

  @Override
  public Object decode(String encoding, Type subjectType) {
    return translator().decode(encoding, subjectType);
  }

  @Override
  public String encode(Object value) {
    return value.toString();
  }

  // ---------------------------
  // Auditing
  // ---------------------------
  public void audit() {
    new TypeAudit(this).audit();
    // Assertion.check(name != null, "%s.name is null", this);
    // Assertion.check(iClass != null, "%s.iClass is null", this);
    // Assertion.check(metatype != null, "%s.metatype is null", this);
    // Class sc = iClass.getSuperclass();
    // if(iClass == String.class)
    // trap = 1;
    // Assertion.check(iClass.getSuperclass() == null || supertype != null,
    // "%s.supertype is null", this);
    //// Assertion.check(!isParametric() || signature != null, "%s.signature is null", this);
    // Assertion.check(primaryId() != null, "%s.primaryId is null", this);
  }

  public TypeAudit auditor() {
    return new TypeAudit(this);
  }

  // ---------------------------
  // Printing
  // ---------------------------
  @Override
  public void print(TextFlow s) {
    printName(s);
    if(showFlags)
      printFlags(s);
  }

  @Override
  public void printName(TextFlow s) {
    s.emit(displayName());
  }

  /**
   * Emits this type's flags.
   */
  public void printFlags(TextFlow s) {
    s.emit(flags());
  }

  // ---------------------------
  // Trace Channel Control
  // ---------------------------
  protected void traceComparison(TypeComparisonKind k, Type t) {
    trace("%s", new TypeComparison(this, t, k));
  }

  /**
   * Sets tracing of this type's instances to <code>on</code>.
   */
  public void instanceTracingEnabled(boolean on) {
    traceChannelFor(iClass).enablement(on);
  }

  // ---------------------------
  // Dumping
  // ---------------------------
  public void dumpScopeTree() {
    printWith(s -> dumpScopeTreeTo(s));
  }

  private void dumpScopeTreeTo(TextFlow s) {
    if(supertype() != null)
      supertype.dumpScopeTreeTo(s);
    s.println_(this);
    s.enter();
  }

  public void dumpTree() {
    dumpWith(s -> {
      for(Type t = this; t != null; t = t.supertype())
        s.format("%s: %s\n", t.baseName(), t.meta().kernelState);
    });
  }

  // ======================================================================
  // Inner Classes
  // ======================================================================
  /****************************************************************************
   * <code>EmptyStructureAspect</code> is a dummy structureAspect for atomic types.
   ****************************************************************************/
  static class EmptyStructureAspect 
    extends StructureAspect
  {
    public FacetFlow<Facet> facets() {
      return new FacetFlow();
    }

    public FieldFlow fields() {
      return new FieldFlow();
    }

    public FacetFlow<Facet> localFacets() {
      return new FacetFlow();
    }
  }

}