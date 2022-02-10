open Names
(** {1 Paths} *)

module Identifier = struct
  type container_page = [ `Page of container_page option * PageName.t ]
  (** @canonical Odoc_model.Paths.Identifier.ContainerPage.t *)

  type page =
    [ container_page | `LeafPage of container_page option * PageName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Page.t *)

  type odoc_id = [ page | `Root of container_page option * ModuleName.t ]
  (** @canonical Odoc_model.Paths.Identifier.OdocId.t *)

  type signature =
    [ `Root of container_page option * ModuleName.t
    | `Module of signature * ModuleName.t
    | `Parameter of signature * ParameterName.t
    | `Result of signature
    | `ModuleType of signature * ModuleTypeName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Signature.t *)

  type class_signature =
    [ `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Identifier.ClassSignature.t *)

  type datatype = [ `Type of signature * TypeName.t | `CoreType of TypeName.t ]
  (** @canonical Odoc_model.Paths.Identifier.DataType.t *)

  type parent = [ signature | datatype | class_signature ]
  (** @canonical Odoc_model.Paths.Identifier.Parent.t *)

  type label_parent = [ parent | page ]
  (** @canonical Odoc_model.Paths.Identifier.LabelParent.t *)

  type root_module = [ `Root of container_page option * ModuleName.t ]
  (** @canonical Odoc_model.Paths.Identifier.RootModule.t *)

  type module_ = [ root_module | `Module of signature * ModuleName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Module.t *)

  type functor_parameter = [ `Parameter of signature * ParameterName.t ]
  (** @canonical Odoc_model.Paths.Identifier.FunctorParameter.t *)

  type functor_result = [ `Result of signature ]
  (** @canonical Odoc_model.Paths.Identifier.FunctorResult.t *)

  type module_type = [ `ModuleType of signature * ModuleTypeName.t ]
  (** @canonical Odoc_model.Paths.Identifier.ModuleType.t *)

  type type_ = [ `Type of signature * TypeName.t | `CoreType of TypeName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Type.t *)

  type constructor = [ `Constructor of type_ * ConstructorName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Constructor.t *)

  type field = [ `Field of parent * FieldName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Field.t *)

  type extension = [ `Extension of signature * ExtensionName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Extension.t *)

  type exception_ =
    [ `Exception of signature * ExceptionName.t
    | `CoreException of ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Exception.t *)

  type value = [ `Value of signature * ValueName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Value.t *)

  type class_ = [ `Class of signature * ClassName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Class.t *)

  type class_type = [ `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Identifier.ClassType.t *)

  type method_ = [ `Method of class_signature * MethodName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Method.t *)

  type instance_variable =
    [ `InstanceVariable of class_signature * InstanceVariableName.t ]
  (** @canonical Odoc_model.Paths.Identifier.InstanceVariable.t *)

  type label = [ `Label of label_parent * LabelName.t ]
  (** @canonical Odoc_model.Paths.Identifier.Label.t *)

  type any =
    [ signature
    | class_signature
    | datatype
    | parent
    | label_parent
    | module_
    | functor_parameter
    | functor_result
    | module_type
    | type_
    | constructor
    | field
    | extension
    | exception_
    | value
    | class_
    | class_type
    | method_
    | instance_variable
    | label
    | page ]
  (** @canonical Odoc_model.Paths.Identifier.t *)

  type path_module = [ module_ | functor_parameter | functor_result ]
  (** @canonical Odoc_model.Paths.Identifier.Path.Module.t *)

  type path_module_type = module_type
  (** @canonical Odoc_model.Paths.Identifier.Path.ModuleType.t *)

  type path_type = [ type_ | class_ | class_type ]
  (** @canonical Odoc_model.Paths.Identifier.Path.Type.t *)

  type path_class_type = [ class_ | class_type ]
  (** @canonical Odoc_model.Paths.Identifier.Path.ClassType.t *)

  type path_any =
    [ path_module | path_module_type | path_type | path_class_type ]
  (** @canonical Odoc_model.Paths.Identifier.Path.t *)

  type fragment_module = path_module

  type fragment_type = path_type

  type reference_module = path_module

  type reference_module_type = path_module_type

  type reference_type = path_type

  type reference_constructor = [ constructor | extension | exception_ ]

  type reference_field = field

  type reference_extension = [ extension | exception_ ]

  type reference_exception = exception_

  type reference_value = value

  type reference_class = class_

  type reference_class_type = [ class_ | class_type ]

  type reference_method = method_

  type reference_instance_variable = instance_variable

  type reference_label = label

  type reference_page = page
end

module rec Path : sig
  type module_ =
    [ `Resolved of Resolved_path.module_
    | `Identifier of Identifier.path_module * bool
    | `Root of string
    | `Forward of string
    | `Dot of module_ * string
    | `Apply of module_ * module_ ]
  (** @canonical Odoc_model.Paths.Path.Module.t *)

  type module_type =
    [ `Resolved of Resolved_path.module_type
    | `Identifier of Identifier.path_module_type * bool
    | `Dot of module_ * string ]
  (** @canonical Odoc_model.Paths.Path.ModuleType.t *)

  type type_ =
    [ `Resolved of Resolved_path.type_
    | `Identifier of Identifier.path_type * bool
    | `Dot of module_ * string ]
  (** @canonical Odoc_model.Paths.Path.Type.t *)

  type class_type =
    [ `Resolved of Resolved_path.class_type
    | `Identifier of Identifier.path_class_type * bool
    | `Dot of module_ * string ]
  (** @canonical Odoc_model.Paths.Path.ClassType.t *)

  type any =
    [ `Resolved of Resolved_path.any
    | `Identifier of Identifier.path_any * bool
    | `Root of string
    | `Forward of string
    | `Dot of module_ * string
    | `Apply of module_ * module_ ]
  (** @canonical Odoc_model.Paths.Path.t *)
end =
  Path

and Resolved_path : sig
  type module_ =
    [ `Identifier of Identifier.path_module
    | `Subst of module_type * module_
    | `Hidden of module_
    | `Module of module_ * ModuleName.t
    | `Canonical of module_ * Path.module_
    | `Apply of module_ * module_
    | `Alias of module_ * module_
    | `OpaqueModule of module_ ]
  (** @canonical Odoc_model.Paths.Path.Resolved.Module.t *)

  and module_type =
    [ `Identifier of Identifier.path_module_type
    | `SubstT of module_type * module_type
    | `CanonicalModuleType of module_type * Path.module_type
    | `AliasModuleType of module_type * module_type
    | `ModuleType of module_ * ModuleTypeName.t
    | `OpaqueModuleType of module_type ]
  (** @canonical Odoc_model.Paths.Path.Resolved.ModuleType.t *)

  type type_ =
    [ `Identifier of Identifier.path_type
    | `CanonicalType of type_ * Path.type_
    | `Type of module_ * TypeName.t
    | `Class of module_ * ClassName.t
    | `ClassType of module_ * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Path.Resolved.Type.t *)

  type class_type =
    [ `Identifier of Identifier.path_class_type
    | `Class of module_ * ClassName.t
    | `ClassType of module_ * ClassTypeName.t ]

  type any =
    [ `Identifier of Identifier.any
    | `Subst of module_type * module_
    | `Hidden of module_
    | `Module of module_ * ModuleName.t
    | `Canonical of module_ * Path.module_
    | `Apply of module_ * module_
    | `Alias of module_ * module_
    | `AliasModuleType of module_type * module_type
    | `OpaqueModule of module_
    | `ModuleType of module_ * ModuleTypeName.t
    | `CanonicalModuleType of module_type * Path.module_type
    | `SubstT of module_type * module_type
    | `OpaqueModuleType of module_type
    | `CanonicalType of type_ * Path.type_
    | `Type of module_ * TypeName.t
    | `Class of module_ * ClassName.t
    | `ClassType of module_ * ClassTypeName.t
    | `Class of module_ * ClassName.t
    | `ClassType of module_ * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Path.Resolved.t *)
end =
  Resolved_path

module rec Fragment : sig
  type signature =
    [ `Resolved of Resolved_fragment.signature
    | `Dot of signature * string
    | `Root ]
  (** @canonical Odoc_model.Paths.Fragment.Signature.t *)

  type module_ =
    [ `Resolved of Resolved_fragment.module_ | `Dot of signature * string ]
  (** @canonical Odoc_model.Paths.Fragment.Module.t *)

  type module_type =
    [ `Resolved of Resolved_fragment.module_type | `Dot of signature * string ]
  (** @canonical Odoc_model.Paths.Fragment.ModuleType.t *)

  type type_ =
    [ `Resolved of Resolved_fragment.type_ | `Dot of signature * string ]
  (** @canonical Odoc_model.Paths.Fragment.Type.t *)

  type leaf =
    [ `Resolved of Resolved_fragment.leaf | `Dot of signature * string ]
  (** @canonical Odoc_model.Paths.Fragment.leaf *)

  type any =
    [ `Resolved of Resolved_fragment.any | `Dot of signature * string | `Root ]
  (** @canonical Odoc_model.Paths.Fragment.t *)
end =
  Fragment

and Resolved_fragment : sig
  type root =
    [ `ModuleType of Resolved_path.module_type
    | `Module of Resolved_path.module_ ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.root *)

  type signature =
    [ `Root of root
    | `Subst of Resolved_path.module_type * module_
    | `Alias of Resolved_path.module_ * module_
    | `Module of signature * ModuleName.t
    | `OpaqueModule of module_ ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.Signature.t *)

  and module_ =
    [ `Subst of Resolved_path.module_type * module_
    | `Alias of Resolved_path.module_ * module_
    | `Module of signature * ModuleName.t
    | `OpaqueModule of module_ ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.Module.t *)

  type type_ =
    [ `Type of signature * TypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.Type.t *)

  and module_type = [ `Module_type of signature * ModuleTypeName.t ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.ModuleType.t *)

  type leaf = [ module_ | module_type | type_ ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.leaf *)

  (* Absence of `Root here might make coersions annoying *)
  type any =
    [ `Root of root
    | `Subst of Resolved_path.module_type * module_
    | `Alias of Resolved_path.module_ * module_
    | `Module of signature * ModuleName.t
    | `Module_type of signature * ModuleTypeName.t
    | `Type of signature * TypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `OpaqueModule of module_ ]
  (** @canonical Odoc_model.Paths.Fragment.Resolved.t *)
end =
  Resolved_fragment

module rec Reference : sig
  type tag_only_module = [ `TModule ]

  type tag_only_module_type = [ `TModuleType ]

  type tag_only_type = [ `TType ]

  type tag_only_constructor = [ `TConstructor ]

  type tag_only_field = [ `TField ]

  type tag_only_extension = [ `TExtension ]

  type tag_only_exception = [ `TException ]

  type tag_only_value = [ `TValue ]

  type tag_only_class = [ `TClass ]

  type tag_only_class_type = [ `TClassType ]

  type tag_only_method = [ `TMethod ]

  type tag_only_instance_variable = [ `TInstanceVariable ]

  type tag_only_label = [ `TLabel ]

  type tag_only_page = [ `TPage ]

  type tag_unknown = [ `TUnknown ]

  type tag_only_child_page = [ `TChildPage ]

  type tag_only_child_module = [ `TChildModule ]

  type tag_any =
    [ `TModule
    | `TModuleType
    | `TType
    | `TConstructor
    | `TField
    | `TExtension
    | `TException
    | `TValue
    | `TClass
    | `TClassType
    | `TMethod
    | `TInstanceVariable
    | `TLabel
    | `TPage
    | `TChildPage
    | `TChildModule
    | `TUnknown ]

  type tag_signature = [ `TUnknown | `TModule | `TModuleType ]

  type tag_class_signature = [ `TUnknown | `TClass | `TClassType ]

  type tag_datatype = [ `TUnknown | `TType ]

  type tag_parent =
    [ `TUnknown | `TModule | `TModuleType | `TClass | `TClassType | `TType ]

  type tag_label_parent =
    [ `TUnknown
    | `TModule
    | `TModuleType
    | `TClass
    | `TClassType
    | `TType
    | `TPage
    | `TChildPage
    | `TChildModule ]

  type signature =
    [ `Resolved of Resolved_reference.signature
    | `Root of string * tag_signature
    | `Dot of label_parent * string
    | `Module of signature * ModuleName.t
    | `ModuleType of signature * ModuleTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Signature.t *)

  and class_signature =
    [ `Resolved of Resolved_reference.class_signature
    | `Root of string * tag_class_signature
    | `Dot of label_parent * string
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.ClassSignature.t *)

  and datatype =
    [ `Resolved of Resolved_reference.datatype
    | `Root of string * tag_datatype
    | `Dot of label_parent * string
    | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.DataType.t *)

  and parent =
    [ `Resolved of Resolved_reference.parent
    | `Root of string * tag_parent
    | `Dot of label_parent * string
    | `Module of signature * ModuleName.t
    | `ModuleType of signature * ModuleTypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Parent.t *)

  and label_parent =
    [ `Resolved of Resolved_reference.label_parent
    | `Root of string * tag_label_parent
    | `Dot of label_parent * string
    | `Module of signature * ModuleName.t
    | `ModuleType of signature * ModuleTypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.LabelParent.t *)

  type module_ =
    [ `Resolved of Resolved_reference.module_
    | `Root of string * [ `TModule | `TUnknown ]
    | `Dot of label_parent * string
    | `Module of signature * ModuleName.t ]
  (** @canonical Odoc_model.Paths.Reference.Module.t *)

  type module_type =
    [ `Resolved of Resolved_reference.module_type
    | `Root of string * [ `TModuleType | `TUnknown ]
    | `Dot of label_parent * string
    | `ModuleType of signature * ModuleTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.ModuleType.t *)

  type type_ =
    [ `Resolved of Resolved_reference.type_
    | `Root of string * [ `TType | `TClass | `TClassType | `TUnknown ]
    | `Dot of label_parent * string
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Type.t *)

  type constructor =
    [ `Resolved of Resolved_reference.constructor
    | `Root of string * [ `TConstructor | `TExtension | `TException | `TUnknown ]
    | `Dot of label_parent * string
    | `Constructor of datatype * ConstructorName.t
    | `Extension of signature * ExtensionName.t
    | `Exception of signature * ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Reference.Constructor.t *)

  type field =
    [ `Resolved of Resolved_reference.field
    | `Root of string * [ `TField | `TUnknown ]
    | `Dot of label_parent * string
    | `Field of parent * FieldName.t ]
  (** @canonical Odoc_model.Paths.Reference.Field.t *)

  type extension =
    [ `Resolved of Resolved_reference.extension
    | `Root of string * [ `TExtension | `TException | `TUnknown ]
    | `Dot of label_parent * string
    | `Extension of signature * ExtensionName.t
    | `Exception of signature * ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Reference.Extension.t *)

  type exception_ =
    [ `Resolved of Resolved_reference.exception_
    | `Root of string * [ `TException | `TUnknown ]
    | `Dot of label_parent * string
    | `Exception of signature * ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Reference.Exception.t *)

  type value =
    [ `Resolved of Resolved_reference.value
    | `Root of string * [ `TValue | `TUnknown ]
    | `Dot of label_parent * string
    | `Value of signature * ValueName.t ]
  (** @canonical Odoc_model.Paths.Reference.Value.t *)

  type class_ =
    [ `Resolved of Resolved_reference.class_
    | `Root of string * [ `TClass | `TUnknown ]
    | `Dot of label_parent * string
    | `Class of signature * ClassName.t ]
  (** @canonical Odoc_model.Paths.Reference.Class.t *)

  type class_type =
    [ `Resolved of Resolved_reference.class_type
    | `Root of string * [ `TClass | `TClassType | `TUnknown ]
    | `Dot of label_parent * string
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.ClassType.t *)

  type method_ =
    [ `Resolved of Resolved_reference.method_
    | `Root of string * [ `TMethod | `TUnknown ]
    | `Dot of label_parent * string
    | `Method of class_signature * MethodName.t ]
  (** @canonical Odoc_model.Paths.Reference.Method.t *)

  type instance_variable =
    [ `Resolved of Resolved_reference.instance_variable
    | `Root of string * [ `TInstanceVariable | `TUnknown ]
    | `Dot of label_parent * string
    | `InstanceVariable of class_signature * InstanceVariableName.t ]
  (** @canonical Odoc_model.Paths.Reference.InstanceVariable.t *)

  type label =
    [ `Resolved of Resolved_reference.label
    | `Root of string * [ `TLabel | `TUnknown ]
    | `Dot of label_parent * string
    | `Label of label_parent * LabelName.t ]
  (** @canonical Odoc_model.Paths.Reference.Label.t *)

  type page =
    [ `Resolved of Resolved_reference.page
    | `Root of string * [ `TPage | `TUnknown ]
    | `Dot of label_parent * string ]
  (** @canonical Odoc_model.Paths.Reference.Page.t *)

  type any =
    [ `Resolved of Resolved_reference.any
    | `Root of string * tag_any
    | `Dot of label_parent * string
    | `Module of signature * ModuleName.t
    | `ModuleType of signature * ModuleTypeName.t
    | `Type of signature * TypeName.t
    | `Constructor of datatype * ConstructorName.t
    | `Field of parent * FieldName.t
    | `Extension of signature * ExtensionName.t
    | `Exception of signature * ExceptionName.t
    | `Value of signature * ValueName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Method of class_signature * MethodName.t
    | `InstanceVariable of class_signature * InstanceVariableName.t
    | `Label of label_parent * LabelName.t ]
  (** @canonical Odoc_model.Paths.Reference.t *)
end =
  Reference

and Resolved_reference : sig
  (* Note - many of these are effectively unions of previous types,
     but they are declared here explicitly because OCaml isn't yet
     smart enough to accept the more natural expression of this. Hence
     we define here all those types that ever appear on the right hand
     side of the constructors and then below we redefine many with
     the actual hierarchy made more explicit. *)
  type datatype =
    [ `Identifier of Identifier.datatype | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.DataType.t *)

  and module_ =
    [ `Identifier of Identifier.path_module
    | `Hidden of module_
    | `Alias of Resolved_path.module_ * module_
    | `Module of signature * ModuleName.t
    | `Canonical of module_ * Reference.module_ ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Module.t *)

  (* Signature is [ module | moduletype ] *)
  and signature =
    [ `Identifier of Identifier.signature
    | `Hidden of module_
    | `Alias of Resolved_path.module_ * module_
    | `Module of signature * ModuleName.t
    | `Canonical of module_ * Reference.module_
    | `ModuleType of signature * ModuleTypeName.t
    | `AliasModuleType of Resolved_path.module_type * module_type ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Signature.t *)

  and class_signature =
    [ `Identifier of Identifier.class_signature
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.ClassSignature.t *)

  (* parent is [ signature | class_signature ] *)
  and parent =
    [ `Identifier of Identifier.parent
    | `Alias of Resolved_path.module_ * module_
    | `AliasModuleType of Resolved_path.module_type * module_type
    | `Module of signature * ModuleName.t
    | `Hidden of module_
    | `Canonical of module_ * Reference.module_
    | `ModuleType of signature * ModuleTypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Parent.t *)

  (* The only difference between parent and label_parent
     is that the Identifier allows more types *)
  and label_parent =
    [ `Identifier of Identifier.label_parent
    | `Alias of Resolved_path.module_ * module_
    | `AliasModuleType of Resolved_path.module_type * module_type
    | `Module of signature * ModuleName.t
    | `Hidden of module_
    | `Canonical of module_ * Reference.module_
    | `ModuleType of signature * ModuleTypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Type of signature * TypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.LabelParent.t *)

  and module_type =
    [ `Identifier of Identifier.reference_module_type
    | `ModuleType of signature * ModuleTypeName.t
    | `AliasModuleType of Resolved_path.module_type * module_type ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.ModuleType.t *)

  type type_ =
    [ `Identifier of Identifier.reference_type
    | `Type of signature * TypeName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Type.t *)

  type constructor =
    [ `Identifier of Identifier.reference_constructor
    | `Constructor of datatype * ConstructorName.t
    | `Extension of signature * ExtensionName.t
    | `Exception of signature * ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Constructor.t *)

  type field =
    [ `Identifier of Identifier.reference_field
    | `Field of parent * FieldName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Field.t *)

  type extension =
    [ `Identifier of Identifier.reference_extension
    | `Extension of signature * ExtensionName.t
    | `Exception of signature * ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Extension.t *)

  type exception_ =
    [ `Identifier of Identifier.reference_exception
    | `Exception of signature * ExceptionName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Exception.t *)

  type value =
    [ `Identifier of Identifier.reference_value
    | `Value of signature * ValueName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Value.t *)

  type class_ =
    [ `Identifier of Identifier.reference_class
    | `Class of signature * ClassName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Class.t *)

  type class_type =
    [ `Identifier of Identifier.reference_class_type
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.ClassType.t *)

  type method_ =
    [ `Identifier of Identifier.reference_method
    | `Method of class_signature * MethodName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Method.t *)

  type instance_variable =
    [ `Identifier of Identifier.reference_instance_variable
    | `InstanceVariable of class_signature * InstanceVariableName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.InstanceVariable.t *)

  type label =
    [ `Identifier of Identifier.reference_label
    | `Label of label_parent * LabelName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Label.t *)

  type page = [ `Identifier of Identifier.reference_page ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.Page.t *)

  type any =
    [ `Identifier of Identifier.any
    | `Alias of Resolved_path.module_ * module_
    | `AliasModuleType of Resolved_path.module_type * module_type
    | `Module of signature * ModuleName.t
    | `Hidden of module_
    | `Canonical of module_ * Reference.module_
    | `ModuleType of signature * ModuleTypeName.t
    | `Type of signature * TypeName.t
    | `Constructor of datatype * ConstructorName.t
    | `Field of parent * FieldName.t
    | `Extension of signature * ExtensionName.t
    | `Exception of signature * ExceptionName.t
    | `Value of signature * ValueName.t
    | `Class of signature * ClassName.t
    | `ClassType of signature * ClassTypeName.t
    | `Method of class_signature * MethodName.t
    | `InstanceVariable of class_signature * InstanceVariableName.t
    | `Label of label_parent * LabelName.t ]
  (** @canonical Odoc_model.Paths.Reference.Resolved.t *)
end =
  Resolved_reference