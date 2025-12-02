import csv
import math
from copy import deepcopy
from typing import List, Any
from collections import deque, defaultdict
import re
import heapq


# Class for a single node in the binary tree
class TreeNode:
    def __init__(self, name, value):
        self.value = value  # Value of the node
        self.name = name
        self.left = None    # Left child
        self.right = None   # Right child

# Class for the binary tree itself
class BinaryTree:
    def __init__(self, root_name, root_value):
        self.root = TreeNode(root_name, root_value)  # Initialize tree with root node

    def build_tree(self, nodes_list, edges_list):
        """
        nodes_list: list of tuples (name, value)
        edges_list: list of tuples (parent, child, 'L'/'R', None)
        """
        # Step 1: Create all TreeNode instances and store in a dictionary
        nodes = {name: TreeNode(name, value) for name, value in nodes_list}

        # Step 2: Attach children based on edges list
        for parent_name, child_name, lr, _ in edges_list:
            parent_node = nodes[parent_name]
            child_node = nodes[child_name]
            if lr == 'L':
                parent_node.left = child_node
            elif lr == 'R':
                parent_node.right = child_node
            else:
                raise ValueError(f"Unknown child direction: {lr}")

        # Step 3: Return the BinaryTree with root
        root_name, root_value = nodes_list[0]  # Assuming first node is root
        self.root = nodes[root_name]

    def level_order_traversal(self):
        """
        Vrátí seznam n-tic (jméno, hodnota) seřazený podle pater (Level-order).
        """
        # 1. Pokud je strom prázdný, vrátíme prázdný seznam
        if self.root is None:
            return []

        result_list = []

        # 2. Inicializace fronty s kořenem
        queue = deque([self.root])

        # 3. Cyklus dokud je ve frontě co zpracovávat
        while queue:
            # Vybereme první prvek z fronty
            current_node = queue.popleft()

            # Vytvoříme n-tici (tuple) a přidáme do výsledného seznamu
            result_list.append((current_node.name, current_node.value))

            # Pokud existují děti, přidáme je na konec fronty
            # Důležité: Tím zajistíme, že se zpracují až po aktuálním patře
            if current_node.left:
                queue.append(current_node.left)
            if current_node.right:
                queue.append(current_node.right)

        # 4. Vrátíme hotový seznam
        return result_list


    # Example method: In-order traversal
    def inorder_traversal(self, node=None):
        if node is None:
            node = self.root
        result = []
        if node.left:
            result.extend(self.inorder_traversal(node.left))
        result.append((node.name, node.value))
        if node.right:
            result.extend(self.inorder_traversal(node.right))
        return result

    # Example method: Pre-order traversal
    def preorder_traversal(self, node=None):
        if node is None:
            node = self.root
        result = [(node.name, node.value)]
        if node.left:
            result.extend(self.preorder_traversal(node.left))
        if node.right:
            result.extend(self.preorder_traversal(node.right))
        return result

    # Example method: Post-order traversal
    def postorder_traversal(self, node=None):
        if node is None:
            node = self.root
        result = []
        if node.left:
            result.extend(self.postorder_traversal(node.left))
        if node.right:
            result.extend(self.postorder_traversal(node.right))
        result.append((node.name, node.value))
        return result

    def insert(self, name=None, value=None):
        """
        Veřejná metoda pro vložení prvku.
        Zavolá pomocnou rekurzivní metodu na kořen.
        """
        if self.root is None:
            self.root = TreeNode(name, value)
        else:
            self._insert_recursive(self.root, name, value)

    def _insert_recursive(self, current_node, name, value):
        """
        Privátní pomocná metoda pro rekurzivní hledání místa.
        """
        # 1. Pokud je nová hodnota menší, jdeme doleva
        if value < current_node.value:
            if current_node.left is None:
                # Našli jsme volné místo -> vytvoříme nový uzel
                current_node.left = TreeNode(name, value)
            else:
                # Místo je obsazené -> zanoříme se hlouběji vlevo
                self._insert_recursive(current_node.left, name, value)

        # 2. Pokud je nová hodnota větší, jdeme doprava
        elif value > current_node.value:
            if current_node.right is None:
                # Našli jsme volné místo -> vytvoříme nový uzel
                current_node.right = TreeNode(name, value)
            else:
                # Místo je obsazené -> zanoříme se hlouběji vpravo
                self._insert_recursive(current_node.right, name, value)

        # 3. Pokud je hodnota stejná (duplicita)
        else:
            print(
                f"Hodnota {value} ({name}) již ve stromu existuje, přeskakuji.")

    def delete(self, value):
        """
        Veřejná metoda pro smazání uzlu podle hodnoty.
        Aktualizuje kořen, kdyby náhodou byl smazán právě on.
        """
        self.root = self._delete_recursive(self.root, value)

    def _delete_recursive(self, current_node, value):
        """
        Rekurzivní metoda, která hledá uzel a řeší 3 případy mazání.
        Vrací (nový) uzel, který má být na tomto místě.
        """
        # 1. Základní případ: Strom je prázdný nebo jsme došli na konec
        if current_node is None:
            return None

        # 2. Hledání uzlu ke smazání
        if value < current_node.value:
            current_node.left = self._delete_recursive(current_node.left, value)
        elif value > current_node.value:
            current_node.right = self._delete_recursive(current_node.right,
                                                        value)

        # 3. Našli jsme uzel (value == current_node.value), jdeme mazat
        else:
            # PŘÍPAD A: Uzel nemá děti (je to list)
            if current_node.left is None and current_node.right is None:
                return None

            # PŘÍPAD B: Uzel má jen jedno dítě
            elif current_node.left is None:
                return current_node.right  # vrátíme pravé dítě o patro výš
            elif current_node.right is None:
                return current_node.left  # vrátíme levé dítě o patro výš

            # PŘÍPAD C: Uzel má dvě děti
            else:
                # Najdeme "následníka" (nejmenší prvek v pravém podstromu)
                min_node = self._find_the_leftest(current_node.right)

                # Zkopírujeme data následníka do aktuálního uzlu (přepíšeme ho)
                current_node.value = min_node.value
                current_node.name = min_node.name  # Důležité: musíme zkopírovat i jméno!

                # Smažeme následníka z pravého podstromu (už jsme ho přesunuli sem)
                current_node.right = self._delete_recursive(current_node.right,
                                                            min_node.value)

        return current_node

    def _find_the_leftest(self, node):
        """
        Pomocná metoda: Jde stále doleva, dokud nenarazí na nejmenší prvek.
        """
        current = node
        while current.left is not None:
            current = current.left
        return current

    def is_valid_bst(self):
        """
        Veřejná metoda, která spustí kontrolu od kořene.
        Používáme nekonečno jako počáteční limity.
        """
        return self._is_valid_recursive(self.root, float('-inf'), float('inf'))

    def _is_valid_recursive(self, node, min_val, max_val):
        """
        Rekurzivní kontrola s limity.
        """
        # 1. Prázdný strom/podstrom je validní BST
        if node is None:
            return True

        # 2. Kontrola aktuálního uzlu vůči limitům
        # Hodnota musí být ostře větší než min_val a menší než max_val
        if not (min_val < node.value < max_val):
            return False

        # 3. Rekurze pro syny
        # Pro levého syna: update horního limitu (musí být menší než aktuální uzel)
        # Pro pravého syna: update dolního limitu (musí být větší než aktuální uzel)
        left_is_valid = self._is_valid_recursive(node.left, min_val, node.value)
        right_is_valid = self._is_valid_recursive(node.right, node.value,
                                                  max_val)

        # Platí jen tehdy, pokud je v pořádku levá I pravá strana
        return left_is_valid and right_is_valid


def export_matrix_to_csv(filename, matrix, row_labels=None, col_labels=None,
                          inf_representation="inf"):
    """
    Exportuje 2D matici do souboru CSV.

    Parametry:
    - filename (str): Název souboru, do kterého se má matice uložit (např. 'length_matrix.csv').
    - matrix (list of lists): Matice (seznam seznamů) k uložení.
    - row_labels (list, volitelné): Seznam názvů pro řádky (např. názvy uzlů).
    - col_labels (list, volitelné): Seznam názvů pro sloupce (např. názvy uzlů).
    - inf_representation (str, volitelné): Reprezentace pro float('inf') v CSV.
    """

    with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.writer(csvfile)

        # 1. Vytvoření hlavičky (názvy sloupců)
        header = []
        if row_labels and col_labels:
            # První buňka hlavičky je prázdná, pokud máme i řádkové labely
            header.append('')

        if col_labels:
            header.extend(col_labels)

        if header:
            writer.writerow(header)

        # 2. Zápis datových řádků
        for i, row in enumerate(matrix):
            output_row = []

            # Přidání řádkového labelu, pokud existuje
            if row_labels:
                output_row.append(row_labels[i])

            # Formátování hodnot v řádku
            for value in row:
                if value == math.inf:
                    # Nahradíme nekonečno specifikovanou textovou reprezentací
                    output_row.append(inf_representation)
                else:
                    # Jinak zapíšeme hodnotu tak, jak je
                    output_row.append(value)

            writer.writerow(output_row)

    print(f"✅ Matice byla úspěšně exportována do '{filename}'.")


def sum_row(matrix, row_index):
    if row_index < 0 or row_index >= len(matrix):
        raise IndexError("Index řádku je mimo rozsah matice.")
    row_sum = sum(matrix[row_index])
    return row_sum

def sum_col(matrix, col_index):
    if col_index < 0 or col_index >= len(matrix):
        raise IndexError("Index řádku je mimo rozsah matice.")
    col_sum = sum([matrix[i][col_index] for i in range(len(matrix))])
    return col_sum


class Graph:
    """
    A class representing a graph with nodes, edges, and various matrix representations.
    """

    def __init__(self):
        # --- Attributes: Components ---
        self.nodes = []  # tuples of name and rank
        self.edges = [] # triplets of name and name

        self.is_oriented = False
        self.is_weighted = False
        self.is_ranked = False
        self.is_bin_tree = False
        self.bin_tree = None

        self.graph_name = None

        # --- Attributes: Matrices (Initialized as empty/None) ---
        # The structure of these matrices will depend on how the graph is populated.
        # They are typically computed/updated after nodes/edges are added.
        self.value_matrix: List[List[Any]] = []
        self.distance_matrix: List[List[float]] = []  # E.g., for shortest paths
        self.adjacency_matrix: List[List[int]] = []  # 1/0 for connectivity
        self.incidence_matrix: List[List[int]] = []  # Nodes x Edges matrix

        self.node_count = 0
        self.edges_count = 0
        self.ones_count = 0
        self.zeroes_count = 0
        self.has_negative_edges = False

    def clear(self):
        self.nodes = []  # tuples of name and rank
        self.edges = [] # triplets of name and name

        self.is_oriented = False
        self.is_weighted = False
        self.is_ranked = False
        self.is_bin_tree = False
        self.bin_tree = None

        self.graph_name = None

        # --- Attributes: Matrices (Initialized as empty/None) ---
        # The structure of these matrices will depend on how the graph is populated.
        # They are typically computed/updated after nodes/edges are added.
        self.value_matrix: List[List[Any]] = []
        self.distance_matrix: List[List[float]] = []  # E.g., for shortest paths
        self.adjacency_matrix: List[List[int]] = []  # 1/0 for connectivity
        self.incidence_matrix: List[List[int]] = []  # Nodes x Edges matrix

        self.node_count = 0
        self.edges_count = 0
        self.ones_count = 0
        self.zeroes_count = 0
        self.has_negative_edges = False

    def parse(self, file_path: str, is_tree: bool = False, graph_name: str = None):
        self.clear()
        self.graph_name = graph_name if graph_name is not None else file_path

        self.is_bin_tree = is_tree
        if not is_tree:
            self._parse_gen_graph(file_path)
        else:
            self._parse_bin_tree(file_path)

    def _parse_bin_tree(self, file_path: str):
        """
        Parses a binary tree from a file in level-order (breadth-first) format.
        Nodes are defined as 'u <identifier>;' or 'u *;' for a missing node.

        Example input:
            u A;
            u B;
            u C;
            u D;
            u E;
            u F;
            u G;
            u H;
            u *;
            u *;
            u *;
            u *;
            u I;
            u *;
            u *;

        Rules:
        1. Nodes are listed level by level.
        2. '*' indicates a missing node.
        3. Edges are created between parent and children automatically.
        """

        # Read file content
        with open(file_path, "r", encoding="utf-8") as f:
            file_content = f.read()

        # Regex to capture node identifier or '*'
        NODE_PATTERN = re.compile(r"u\s+([\w*]+)(?:\s+([-+]?\d*\.?\d+))?\s*;")

        node_list = []
        edge_list = []

        # Extract nodes in order
        nodes_raw = NODE_PATTERN.findall(file_content)

        # Create node list and assign IDs
        for n in nodes_raw:
            if n == '*':
                node_list.append(('*', None))  # Use None for missing nodes
            else:
                # if n.length() == 2:
                #     node_list.append((n.group(1).strip(), n.group(2).strip()))
                # else:
                #     node_list.append((n.group(1).strip(), None))
                name, value = n
                node_list.append((name, float(value) if value is not None and value != '' else None))

        # Build edges using level-order logic
        queue = deque()

        # Start with the root node (first in the list)
        if node_list and node_list[0] is not None:
            queue.append((0, node_list[0][0], node_list[0][1]))  # (index, node_name)

        idx = 1  # Index of next node to process

        while queue:

            parent_data = queue.popleft()
            parent_idx, parent_name, parent_value = parent_data
            # parent_name, parent_value = parent_node_data

            # Left child
            if idx < len(node_list) and node_list[idx] is not None:
                left_name = node_list[idx][0]
                left_value = node_list[idx][1]
                if left_name is not None:
                    edge_list.append((parent_name, left_name, 'L',
                                      None))  # direction 'L' for left
                    queue.append((idx, left_name, float(left_value) if left_value != '' and left_value is not None else None))
                idx += 1

            # Right child
            if idx < len(node_list) and node_list[idx] is not None:
                right_name = node_list[idx][0]
                right_value = node_list[idx][1]
                if right_name is not None:
                    edge_list.append((parent_name, right_name, 'R',
                                      None))  # direction 'R' for right
                    queue.append((idx, right_name, float(right_value) if right_value != '' and right_value is not None else None))
                idx += 1

        # Filter out None nodes from node_list for final storage

        self.nodes = [n for n in sorted(node_list) if n is not None]
        self.edges = edge_list

        self.bin_tree = BinaryTree(None, None)
        self.bin_tree.build_tree(nodes_list=self.nodes, edges_list=self.edges)

        self.incidence_matrix = None
        self.adjacency_matrix = None
        self.distance_matrix = None
        self.node_count = len(self.nodes)

    def _parse_gen_graph(self, file_path: str):
        """
        Parses the custom graph format from a file, extracting node identifiers/weights
        and edges (u1, u2, direction, and edge_name).
        """

        # Read file content
        with open(file_path, "r", encoding="utf-8") as f:
            file_content = f.read()

        # 1. Regex for Node Definition (u)
        # Group 1: identifier, Group 2: optional weight
        NODE_PATTERN = re.compile(r"u\s+(\w+)\s*\[?\s*([^\]]*)\s*\]?\s*;")

        # 2. Regex for Edge Definition (h)
        # Group 1: u1, Group 2: direction, Group 3: u2
        # Group 4: optional weight, Group 5: optional name

        node_list = []

        # Process the file content line by line
        for line in file_content.strip().split(';'):
            if not line.strip():
                continue

            full_line = line.strip() + ';'

            # --- Node ---
            node_match = NODE_PATTERN.match(full_line)
            if node_match:
                identifier = node_match.group(1).strip()
                weight = node_match.group(2).strip()
                weight = weight if weight else None
                node_list.append((identifier, weight))
                continue

            # --- Edge ---
            else:
                parts = line.split()
                u = parts[1].replace(';', '').strip()
                direction = parts[2]
                v = parts[3].replace(';', '').strip()

                # bez nastavování "implicitní 1" do dat – pouze rozlišení váženosti
                edge_name = None

                w = None
                weight_str = None

                if len(parts) == 6:
                    w = float(parts[4])
                    self.is_weighted = True
                    has_w = True

                    edge_name = parts[5].replace(":", "").replace(';', '')
                    weight_str = parts[4].replace(';', '').strip()

                elif len(parts) > 4 and parts[4] and is_float(parts[4].replace(";", "")):
                    weight_str = parts[4].replace(";", "")

                    self.is_weighted = True
                    has_w = True
                else:
                    if len(parts) > 4:
                        edge_name = parts[4].replace(";", "").replace(":", "")
                    has_w = False

                if weight_str and weight_str.isdecimal():
                    w = int(weight_str)
                elif weight_str and is_float(weight_str):
                    w = float(weight_str)

                if weight_str is None:
                    if v == u:
                        w = 0
                    else:
                        w = 1

                if w is not None and w < 0:
                    self.has_weight = True

                if direction == '>':
                    self.edges.append((u, v, w, edge_name))
                    self.is_oriented = True
                elif direction == '<':
                    self.edges.append((v, u, w, edge_name))
                    self.is_oriented = True
                elif direction == '-':
                    self.edges.append((u, v, w, edge_name))
                else:
                    # neznámý formát
                    pass
        # print(self.edges)
        self.nodes = sorted(node_list)
        # print(self.nodes)
        self.bin_tree = None
        self.calculate_node_matrix(adjacency=True)
        self.calculate_node_matrix(adjacency=False)
        self.calculate_incidence_matrix()
        self.node_count = len(self.nodes)
        self.edges_count = len(self.edges)
        self.ones_count = sum([self.adjacency_matrix[i][i] for i in range(self.node_count)])
        self.zeroes_count = self.node_count - self.ones_count

    def _translate_node_index_to_name(self, index):
        names = self._translate_node_indices_to_names(index)
        if names:
            return names[0]
        return None

    def _translate_node_indices_to_names(self, indices):
        node_names = [node[0] for node in self.nodes]
        names = []
        for index in indices:
            names.append(node_names[index])
        return names

    def _translate_node_names_to_indices(self, names):
        indices = []
        node_names = [node[0] for node in self.nodes]
        for name in names:
            indices.append(node_names.index(name))
        return indices

    def calculate_node_matrix(self, adjacency=True):
        node_names = [node[0] for node in self.nodes]
        index = {v: i for i, v in enumerate(node_names)}

        # initialize empty matrix
        n = len(self.nodes)
        if not adjacency:
            matrix = [[math.inf for _ in range(n)] for _ in range(n)]
            for i in range(n):
                matrix[i][i] = 0
        else:
            matrix = [[0 for _ in range(n)] for _ in range(n)]

        for u, v, w, _ in self.edges:

            i, j = index[u], index[v]

            if adjacency:
                matrix[i][j] += 1
            else:
                matrix[i][j] = w

            if not self.is_oriented:
                matrix[j][i] = matrix[i][j]

        if adjacency:
            self.adjacency_matrix = matrix
        else:
            self.distance_matrix = matrix

    def calculate_incidence_matrix(self):
        """
        Calculates the Incidence Matrix (Vertex x Edge) using pure Python.
        """
        # 1. Identify distinct sorted vertices (Rows)
        vertices = [node[0] for node in self.nodes]

        sorted_vertices = list(vertices)
        n_vertices = len(sorted_vertices)
        n_edges = len(self.edges)

        # Map vertex label to row index
        v_to_i = {v: i for i, v in enumerate(sorted_vertices)}

        # 2. Initialize V x E matrix with 0
        # Rows = Vertices, Columns = Edges
        matrix = [[0] * n_edges for _ in range(n_vertices)]

        # 3. Fill the matrix
        for col_index, edge in enumerate(self.edges):
            u, v = edge[0], edge[1]

            # Check orientation
            # If None/False -> Undirected. If True -> Directed.
            is_oriented = edge[3] if len(edge) > 3 else False

            row_u = v_to_i[u]
            row_v = v_to_i[v]

            if is_oriented:
                # Directed: Source gets -1, Target gets 1
                matrix[row_u][col_index] = -1
                matrix[row_v][col_index] = 1
            else:
                # Undirected: Both endpoints get 1
                matrix[row_u][col_index] = 1
                matrix[row_v][col_index] = 1

        self.incidence_matrix = matrix

    def export_matrices(self):
        node_names = [node[0] for node in self.nodes]
        export_matrix_to_csv(
            self.graph_name + "_adjacency_matrix.csv", self.adjacency_matrix,
            node_names,
            node_names
        )
        export_matrix_to_csv(
            self.graph_name + "_distance_matrix.csv", self.distance_matrix,
            node_names,
            node_names
        )
        edges_names = [
            "(" + edge[0] + ", " + edge[1] + ")" if edge[3] is None else edge[3]
            in self.edges for edge in self.edges
        ]
        export_matrix_to_csv(
            self.graph_name + "_incidence_matrix.csv", self.incidence_matrix,
            node_names,
            node_names
        )

    def is_multigraph(self):
        for radek in self.adjacency_matrix:
            for prvek in radek:
                if prvek > 1:
                    return True
        return False

    def has_self_loop(self):
        return self.ones_count > 0

    # def is_complete(self):
    #     adj_list = defaultdict(set)
    #     for e in self.edges:
    #         u, v = edge_uv(e)
    #         adj_list[u].add(v)
    #         if not self.is_oriented:
    #             adj_list[v].add(u)
    #     for u in self.nodes:
    #         for v in self.nodes:
    #             if u != v and v not in adj_list[u]:
    #                 return False
    #     return True

    def is_complete(self):
        n = len(self.adjacency_matrix)  # Počet vrcholů

        # Prázdný graf nebo graf s jedním vrcholem je triviálně úplný
        if n <= 1:
            return True

            # 2. Kontrola všech prvků matice pomocí vnořených cyklů
        for i in range(n):
            for j in range(n):
                if i == j:
                    # Na hlavní diagonále: Očekáváme 0 (žádné smyčky)
                    if self.adjacency_matrix[i][j] != 0:
                        return False
                else:
                    # Mimo hlavní diagonálu: Očekáváme 1 (spojení každé dvojice)
                    if self.adjacency_matrix[i][j] != 1:
                        return False

        # Pokud cykly proběhnou bez nalezení chyby, graf je úplný
        return True

    def get_sum_adjacency_matrix_row(self, node_name="A"):
        row_index = [node[0] for node in self.nodes].index(node_name)
        return sum_row(self.adjacency_matrix, row_index=row_index)

    def get_sum_adjacency_matrix_col(self, node_name):
        col_index = [node[0] for node in self.nodes].index(node_name)
        return sum_col(self.adjacency_matrix, col_index=col_index)

    def get_sum_distance_matrix_row(self, node_name):
        row_index = [node[0] for node in self.nodes].index(node_name)
        return sum_row(self.distance_matrix, row_index=row_index)

    def get_sum_distance_matrix_col(self, node_name):
        col_index = [node[0] for node in self.nodes].index(node_name)
        return sum_col(self.distance_matrix, col_index=col_index)

    def get_sum_incidence_matrix_row(self, node_name):
        row_index = [node[0] for node in self.nodes].index(node_name)
        return sum_row(self.incidence_matrix, row_index=row_index)

    def get_sum_incidence_matrix_col(self, edge_name):
        col_index = [node[3] if node[3] is not None else (node[0], node[1]) for node in self.edges].index(edge_name)
        return sum_col(self.distance_matrix, col_index=col_index)

    def is_connected(self):
        if not self.nodes:
            return True
        nodes = [node[0] for node in self.nodes]
        adj_list = defaultdict(list)
        for e in self.edges:
            u, v = edge_uv(e)
            adj_list[u].append(v)
            adj_list[v].append(u)
        start = nodes[0]
        vis = {start}
        dq = deque([start])
        while dq:
            x = dq.popleft()
            for y in adj_list[x]:
                if y not in vis:
                    vis.add(y)
                    dq.append(y)
        return len(vis) == len(nodes)

    def is_strongly_connected(self):
        n = len(self.nodes)
        nodes = [node[0] for node in self.nodes]
        visited = [False] * n

        def dfs(v):
            visited[v] = True
            for i in range(n):
                if self.adjacency_matrix[v][i] == 1 and not visited[i]:
                    dfs(i)

        for start_node in range(n):
            visited = [False] * n
            dfs(start_node)
            if not all(visited):
                return False
        return True

    def is_simple(self):
        for i in range(len(self.adjacency_matrix)):
            for j in range(len(self.adjacency_matrix)):
                if i != j and self.adjacency_matrix[i][j] > 1:
                    return False
        return True

    def is_plain(self):
        n = len(self.adjacency_matrix)
        for i in range(n):
            if self.adjacency_matrix[i][i] != 0:
                return False
        return True

    def is_regular(self):
        n = len(self.adjacency_matrix)
        if self.is_oriented:
            out_degrees = [sum(row) for row in self.adjacency_matrix]
            in_degrees = [sum(self.adjacency_matrix[i][j] for i in range(n)) for j in range(n)]
            return len(set(out_degrees)) == 1 and len(set(in_degrees)) == 1
        else:
            degrees = [sum(row) for row in self.adjacency_matrix]
            return len(set(degrees)) == 1

    def is_bipartite(self):
        n = len(self.adjacency_matrix)
        color = [-1] * n

        def dfs(v, c):
            color[v] = c
            for i in range(n):
                if self.adjacency_matrix[v][i] == 1:
                    if color[i] == -1:
                        if not dfs(i, 1 - c):
                            return False
                    elif color[i] == color[v]:
                        return False
            return True

        for i in range(n):
            if color[i] == -1:
                if not dfs(i, 0):
                    return False
        return True

    def is_reflexive(self):
        n = len(self.adjacency_matrix)
        for i in range(n):
            if self.adjacency_matrix[i][i] != 1:
                return False
        return True

    def print_properties(self):

        print("\nPocet uzlu: " + str(self.node_count))
        print("\nUzly: ", end="")
        print(self.nodes)
        print("Pocet hran: " + str(self.edges_count))

        print("Orientovany: " + str(self.is_oriented))
        is_multigraph_bool = self.is_multigraph()
        print("Multigraf: " + str(is_multigraph_bool))
        if is_multigraph_bool:
            RED = "\033[91m"
            END = "\033[0m"
            print(
                f"{RED}Bacha, graf je multigraf a algoritmy zalozene na matici sousednosti nemusi fungovat spravne{END}")

        if self.is_complete():
            print("Uplny: True")
            print("Souvisly: True") # TODO: check this, uplny graf je souvisly
            print("Regularni: True")
        else:
            print("Uplny: False")
            print("Regularni: " + str(self.is_regular()))
            connected = self.is_connected()
            strongly_connected = self.is_strongly_connected()
            if strongly_connected and connected:
                print("Souvisly: True - Souvisly silne")
            elif connected and not strongly_connected and self.is_oriented:
                print("Souvisly: True - Souvisly slabe")
            elif connected and not strongly_connected and not self.is_oriented:
                print("Slabe souvisly: True")
            else:
                print("Souvisly: False")

        print("Má smyčky: " + str(self.has_self_loop()))
        print("Má 1 na celé diagonále: " + str(self.is_reflexive()))

        if self.is_simple():
            print("Prosty: True")
            if self.is_plain():
                print("Jednoduchy: True")
        else:
            print("Prosty: False")
            print("Jednoduchy: False")
        print("Bipartitni:" + str(self.is_bipartite()))

        print("Hranove ohodnoceny: " + str(self.is_weighted))
        print("Uzlove ohodnoceny: " + str(self.is_ranked))

    def print_node_properties(self, node_name):
        edge_labels = []

        if self.edges != [] and self.edges[0][3] is not None:
            edge_labels = [e[3] for e in self.edges]

        neighbors = defaultdict(list)
        in_neighbors = defaultdict(list)
        out_neighbors = defaultdict(list)
        degree = defaultdict(int)
        in_degree = defaultdict(int)
        out_degree = defaultdict(int)
        predecessors = defaultdict(list)
        successors = defaultdict(list)

        okoli = set()

        for idx, e in enumerate(self.edges):
            u, v = edge_uv(e)
            if edge_labels is None or edge_labels == []:
                edge_label = "gen_h" + str(idx + 1) + "-" + u + "->" + v
            else:
                edge_label = edge_labels[idx]
            if self.is_oriented:
                out_neighbors[u].append(edge_label)
                in_neighbors[v].append(edge_label)
                successors[u].append(v)
                predecessors[v].append(u)
                out_degree[u] += 1
                in_degree[v] += 1
            else:
                okoli.add(edge_label)
                neighbors[u].append(v)
                neighbors[v].append(u)
                degree[u] += 1
                degree[v] += 1

        if self.is_oriented:
            print(
                "Vstupni okoli pro uzel " + str(
                    in_neighbors.get(node_name, [])))
            print("Vystupni okoli pro uzel " + str(
                out_neighbors.get(node_name, [])))
            print("Vstupni stupen uzlu " + str(in_degree.get(node_name, 0)))
            print("Vystupni stupen uzlu " + str(out_degree.get(node_name, 0)))
            print("Predchudci uzlu " + str(predecessors.get(node_name, [])))
            print("Naslednici uzlu " + str(successors.get(node_name, [])))
        else:
            print("Okoli ", end="")
            print(okoli)
            print("Sousede uzlu " + str(neighbors.get(node_name, [])))
            print("Stupen uzlu " + str(degree.get(node_name, 0)))

    def get_count_paths_matrix(self, length):
        # u neorientovaného zajistíme symetrii (pro účely počítání cest)
        adj_matrix = self.adjacency_matrix
        if not self.is_oriented:
            size = self.node_count
            for i in range(size):
                for j in range(i + 1, size):
                    if adj_matrix[i][j] == 1 or adj_matrix[j][i] == 1:
                        adj_matrix[i][j] = adj_matrix[j][i] = 1
        powered_matrix = matrix_power(adj_matrix, length)
        export_matrix_to_csv(self.graph_name + "matrix_power.csv", powered_matrix)
        return powered_matrix

    def get_count_paths_between(self, node1, node2, length):
        paths_matrix = self.get_count_paths_matrix(length)
        node_names = [node[0] for node in self.nodes]
        node1_idx = node_names.index(node1)
        node2_idx = node_names.index(node2)
        return paths_matrix[node1_idx][node2_idx]

    def minimum_spanning_tree(self):
        node_names = [n[0] for n in self.nodes]
        mst, total_weight = kruskal_mst(node_names, self.edges, reverse=False)
        print("Minimální kostra:")
        for u, v, weight in mst:
            print("Hrana:" + str(u) + "-" + str(v) + ", Váha: " + str(weight))
        print("Celková váha: " + str(total_weight))
        return mst, total_weight

    def maximum_spanning_tree(self):
        node_names = [n[0] for n in self.nodes]
        mst, total_weight = kruskal_mst(node_names, self.edges, reverse=True)
        print("Maximální kostra:")
        for u, v, weight in mst:
            print("Hrana:" + str(u) + "-" + str(v) + ", Váha: " + str(weight))
        print("Celková váha: " + str(total_weight))
        return mst, total_weight

    def get_spanning_tree_count(self):
        lap_matrix = laplacian_matrix(self.adjacency_matrix)
        reduced = minor(lap_matrix, 0, 0)
        return abs(determinant(reduced))

    def print_shortest_path(self, node1, node2, floydwarshall=False):
        distance, path = self.find_shortest_path(node1, node2, floydwarshall=floydwarshall)
        node_names = [n[0] for n in self.nodes]
        if distance:
            print("Length: " + str(distance))
            # print("Path: " + str("->".join(path)))
            path_names = [node_names[i] for i in path]
            print("Path: " + str(" -> ".join(path_names)))
        else:
            print("Cesta neexistuje")

    def find_shortest_path(self, node1, node2, floydwarshall=False):
        distances, paths = self._find_shortest_paths(node1, floydwarshall=floydwarshall)
        node_names = [n[0] for n in self.nodes]
        node_idx = node_names.index(node2)
        if floydwarshall:
            return distances[node_idx], paths[node_idx]
        if distances:
            dist = list(filter(lambda d: d is not None and d[0] == node2, distances))
            if dist != [] and dist[0][1] != math.inf:
                path = list(filter(lambda d: d is not None and d[-1] == node_idx, paths))
                return dist[0][1], path[0]
        return None, None

    def _find_shortest_paths(self, node_name, floydwarshall=False):
        node_names = [n[0] for n in self.nodes]
        node_idx = node_names.index(node_name)
        if floydwarshall:
            dist, paths = floyd_warshall(self.distance_matrix)
            return dist, paths
        if self.has_negative_edges:
            dist, path = bellman_ford(self.distance_matrix, node_idx)
            return list(zip(node_names, dist)), path
        else:
            dist, path = dijkstra(self.distance_matrix, node_idx)
            return list(zip(node_names, dist)), path

    def max_flow(self, source, sink):
        node_names = [n[0] for n in self.nodes]
        source_idx = node_names.index(source)
        sink_idx = node_names.index(sink)
        capacity_matrix = []
        for row in self.distance_matrix:
            r = []
            for n in row:
                if n == math.inf:
                    r.append(0)
                elif n >= 0:
                    r.append(n)
                else:
                    ValueError("Matice obsahuje zápornou kapacitu")
                    return
            capacity_matrix.append(r)

        export_matrix_to_csv(self.graph_name + "_capacity_matrix.csv", capacity_matrix, row_labels=node_names, col_labels=node_names)

        max_flow = goldberg_max_flow(capacity_matrix, source_idx, sink_idx)

        print("Max flow: " + str(max_flow))

    def do_nodes_exist(self, nodes):
        node_names = [n[0] for n in self.nodes]
        for node in nodes:
            if node not in node_names:
                return False
        return True


def goldberg_max_flow(C, s, t):
    """
    Computes the maximum flow in a network using the Push-Relabel (Goldberg) algorithm.

    :param C: Adjacency matrix (List of Lists) where C[u][v] is the capacity of edge u->v.
    :param s: Index of the source node.
    :param t: Index of the sink node.
    :return: The maximum flow value (integer/float).
    """
    n = len(C)  # Number of nodes
    F = [[0] * n for _ in range(n)]  # Flow matrix
    height = [0] * n
    excess = [0] * n

    def push(u, v):
        d = min(excess[u], C[u][v] - F[u][v])
        F[u][v] += d
        F[v][u] -= d
        excess[u] -= d
        excess[v] += d

    def relabel(u):
        min_height = float('inf')
        for v in range(n):
            if C[u][v] - F[u][v] > 0:
                min_height = min(min_height, height[v])
        height[u] = min_height + 1

    def discharge(u):
        while excess[u] > 0:
            pushed = False
            for v in range(n):
                if C[u][v] - F[u][v] > 0 and height[u] > height[v]:
                    push(u, v)
                    pushed = True
                    if excess[u] == 0:
                        break
            if not pushed:
                relabel(u)

    # --- Initialization ---
    height[s] = n
    excess[s] = float('inf')

    # Pre-flow: Push max capacity from source to all neighbors
    for v in range(n):
        if C[s][v] > 0:
            push(s, v)

    # --- Main Loop (Relabel-to-Front heuristic) ---
    p = 0
    while p < n:
        if p != s and p != t and excess[p] > 0:
            old_height = height[p]
            discharge(p)
            if height[p] > old_height:
                # If node was relabeled, move to front of list to check dependencies again
                p = 0
            else:
                p += 1
        else:
            p += 1

    return excess[t]


def floyd_warshall(matrix):
    n = len(matrix)

    # distance matrix (copy input)
    dist = [row[:] for row in matrix]

    # next[i][j] = next node on the shortest path from i to j
    next_node = [[None] * n for _ in range(n)]

    for i in range(n):
        for j in range(n):
            if matrix[i][j] != math.inf and i != j:
                next_node[i][j] = j

    # main Floyd–Warshall loop
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if dist[i][k] + dist[k][j] < dist[i][j]:
                    dist[i][j] = dist[i][k] + dist[k][j]
                    next_node[i][j] = next_node[i][k]

    # detect negative cycles
    for i in range(n):
        if dist[i][i] < 0:
            raise ValueError("Negative cycle detected")

    # function to reconstruct path using next_node
    def construct_path(u, v):
        if next_node[u][v] is None:
            return None  # no path
        path = [u]
        while u != v:
            u = next_node[u][v]
            path.append(u)
        return path

    # build full path matrix
    paths = [
        [construct_path(i, j) for j in range(n)]
        for i in range(n)
    ]

    return dist, paths



def bellman_ford(matrix, start):
    n = len(matrix)
    dist = [math.inf] * n
    parent = [-1] * n

    dist[start] = 0

    # Relax edges up to n-1 times
    for _ in range(n - 1):
        updated = False
        for u in range(n):
            for v in range(n):
                w = matrix[u][v]
                if w == math.inf:
                    continue
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    parent[v] = u
                    updated = True
        if not updated:
            break

    # Check for negative cycles
    for u in range(n):
        for v in range(n):
            w = matrix[u][v]
            if w == math.inf:
                continue
            if dist[u] + w < dist[v]:
                raise ValueError("Negative cycle detected")

    # reconstruct paths
    paths = []
    for target in range(n):
        if dist[target] == math.inf:
            paths.append(None)
            continue

        path = []
        cur = target
        while cur != -1:
            path.append(cur)
            cur = parent[cur]
        path.reverse()
        paths.append(path)

    return dist, paths


def dijkstra(matrix, start):
    n = len(matrix)
    dist = [math.inf] * n
    parent = [-1] * n
    visited = [False] * n

    dist[start] = 0
    pq = [(0, start)]

    while pq:
        current_dist, u = heapq.heappop(pq)

        if visited[u]:
            continue
        visited[u] = True

        for v in range(n):
            weight = matrix[u][v]
            if weight == math.inf:
                continue

            # normal Dijkstra relaxation
            if dist[u] + weight < dist[v]:
                dist[v] = dist[u] + weight
                parent[v] = u
                heapq.heappush(pq, (dist[v], v))

    # reconstruct paths for every node
    paths = []
    for target in range(n):
        if dist[target] == math.inf:
            paths.append(None)  # unreachable
            continue

        path = []
        cur = target
        while cur != -1:
            path.append(cur)
            cur = parent[cur]
        path.reverse()
        paths.append(path)

    return dist, paths


def degree_matrix(adj_matrix):
    n = len(adj_matrix)
    degree_mat = [[0] * n for _ in range(n)]
    for i in range(n):
        degree = sum(adj_matrix[i])
        degree_mat[i][i] = degree
    return degree_mat


def laplacian_matrix(adj_matrix):
    n = len(adj_matrix)
    degree_mat = degree_matrix(adj_matrix)
    laplacian = []
    for i in range(n):
        row = []
        for j in range(n):
            row.append(degree_mat[i][j] - adj_matrix[i][j])
        laplacian.append(row)
    return laplacian


def minor(matrix, row, col):
    return [[matrix[i][j] for j in range(len(matrix[i])) if j != col]
            for i in range(len(matrix)) if i != row]


def determinant(matrix):
    if len(matrix) == 1:
        return matrix[0][0]
    if len(matrix) == 2:
        return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    det = 0
    for col in range(len(matrix)):
        sign = 1 if col % 2 == 0 else -1
        det += sign * matrix[0][col] * determinant(minor(matrix, 0, col))
    return det

def kruskal_mst(nodes, edges, reverse=False):
    parent = {u: u for u in nodes}
    rank = {u: 0 for u in nodes}

    def find(x):
        if parent[x] != x:
            parent[x] = find(parent[x])
        return parent[x]

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra == rb:
            return False
        if rank[ra] < rank[rb]:
            parent[ra] = rb
        elif rank[ra] > rank[rb]:
            parent[rb] = ra
        else:
            parent[rb] = ra
            rank[ra] += 1
        return True

    sorted_edges = sorted(iter_edges_with_w(edges, 1), key=lambda x: x[2],
                          reverse=reverse)
    mst, total = [], 0
    for u, v, w in sorted_edges:
        if union(u, v):
            mst.append((u, v, w))
            total += w
    return mst, total


def iter_edges_with_w(edges, default=1):
    """Iterátor, který vrací trojice (u, v, w) i pro nevážené hrany (w=default)."""
    for e in edges:
        u, v = e[0], e[1]
        w = e[2] if e[2] is not None else default
        yield u, v, w


def matrix_multiply(matrix1, matrix2):
    size = len(matrix1)
    result = [[0 for _ in range(size)] for _ in range(size)]
    for i in range(size):
        for j in range(size):
            result[i][j] = sum(
                matrix1[i][k] * matrix2[k][j] for k in range(size))
    return result


def matrix_power(matrix, power):
    size = len(matrix)
    # identita
    result = [[1 if i == j else 0 for j in range(size)] for i in range(size)]
    for _ in range(power):
        result = matrix_multiply(result, matrix)
    return result


def edge_uv(e):
    return e[0], e[1]

def is_float(s):
    """Checks if a string 's' can be safely converted to a float."""
    try:
        float(s)
        return True
    except ValueError:
        return False

graph = Graph()
# TREE = False
# if TREE:
#     graph.parse(file_path="tree.tg", is_tree=True)
# else:
#     graph.parse(file_path="graph.tg")
    # graph.print_properties()
    # graph.export_matrices()
    # print(floyd_warshall(graph.distance_matrix))
