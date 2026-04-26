"""
Enhanced name resolution analysis for better NAME_ERROR handling.
"""
import ast
from typing import Optional, Set


def analyze_local_definitions(fn_node: ast.FunctionDef) -> Set[str]:
    """Analyze a function to find locally defined variables."""
    
    class LocalDefFinder(ast.NodeVisitor):
        def __init__(self):
            self.defined_vars = set()
            
        def visit_Assign(self, node):
            # Handle assignments like: x = ..., a, b = ..., etc.
            for target in node.targets:
                self._extract_names(target)
            self.generic_visit(node)
            
        def visit_AnnAssign(self, node):
            # Handle annotated assignments: x: int = ...
            if node.target:
                self._extract_names(node.target)
            self.generic_visit(node)
            
        def visit_AugAssign(self, node):
            # Handle augmented assignments: x += ...
            self._extract_names(node.target)
            self.generic_visit(node)
            
        def visit_For(self, node):
            # Handle for loop targets: for x in ..., for a, b in ...
            self._extract_names(node.target)
            self.generic_visit(node)
            
        def visit_With(self, node):
            # Handle with statement targets: with ... as x
            for item in node.items:
                if item.optional_vars:
                    self._extract_names(item.optional_vars)
            self.generic_visit(node)
            
        def visit_ListComp(self, node):
            # Handle list comprehensions: [expr for target in iter]
            for generator in node.generators:
                self._extract_names(generator.target)
            self.generic_visit(node)
            
        def visit_SetComp(self, node):
            # Handle set comprehensions: {expr for target in iter}  
            for generator in node.generators:
                self._extract_names(generator.target)
            self.generic_visit(node)
            
        def visit_DictComp(self, node):
            # Handle dict comprehensions: {key: value for target in iter}
            for generator in node.generators:
                self._extract_names(generator.target)
            self.generic_visit(node)
            
        def visit_GeneratorExp(self, node):
            # Handle generator expressions: (expr for target in iter)
            for generator in node.generators:
                self._extract_names(generator.target)
            self.generic_visit(node)
            
        def visit_ExceptHandler(self, node):
            # Handle exception handlers: except Exception as e
            if node.name:
                self.defined_vars.add(node.name)
            self.generic_visit(node)
            
        def _extract_names(self, node):
            """Extract variable names from assignment targets."""
            if isinstance(node, ast.Name):
                self.defined_vars.add(node.id)
            elif isinstance(node, (ast.Tuple, ast.List)):
                for elt in node.elts:
                    self._extract_names(elt)
            # Could handle more complex patterns like starred expressions
    
    # Add function parameters
    finder = LocalDefFinder()
    for arg in fn_node.args.args:
        finder.defined_vars.add(arg.arg)
    
    # Add *args and **kwargs if present
    if fn_node.args.vararg:
        finder.defined_vars.add(fn_node.args.vararg.arg)
    if fn_node.args.kwarg:
        finder.defined_vars.add(fn_node.args.kwarg.arg)
        
    # Analyze function body
    for stmt in fn_node.body:
        finder.visit(stmt)
        
    return finder.defined_vars


def is_name_locally_defined(var_name: str, fn_node: Optional[ast.FunctionDef]) -> bool:
    """Check if a variable name is likely to be defined locally in the function."""
    if not fn_node:
        return False
        
    local_defs = analyze_local_definitions(fn_node)
    return var_name in local_defs