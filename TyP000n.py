#!/usr/bin/env python3
import asyncio
import aiohttp
import aiodns
import ssl
import socket
import whois
import argparse
import re
import string
import difflib
import time
import datetime
import concurrent.futures

try:
    import ssdeep
except ImportError:
    ssdeep = None

# Global variable for dynamic misspelling dictionary (if provided via file)
MISSPELLING_DICT = {}

#######################################
# Variant Generation Functions (Synchronous)
#######################################

def generate_typo_variants(domain):
    """Insertion, deletion, substitution, transposition, homoglyph replacement."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]

    # Insertion: Insert every letter at each position
    for i in range(len(base) + 1):
        for ch in string.ascii_lowercase:
            new_variant = base[:i] + ch + base[i:]
            variants.add(new_variant + '.' + tld)

    # Deletion: Remove each character one by one
    for i in range(len(base)):
        new_variant = base[:i] + base[i+1:]
        variants.add(new_variant + '.' + tld)

    # Substitution: Replace characters with similar-looking ones
    similar_chars = {'o': '0', 'l': '1', 'i': '1', 'a': '@', 'e': '3'}
    for i, ch in enumerate(base):
        if ch in similar_chars:
            new_variant = base[:i] + similar_chars[ch] + base[i+1:]
            variants.add(new_variant + '.' + tld)

    # Transposition: Swap adjacent characters
    for i in range(len(base) - 1):
        lst = list(base)
        lst[i], lst[i+1] = lst[i+1], lst[i]
        variants.add(''.join(lst) + '.' + tld)

    # Homoglyph Replacement: Replace with visually similar Unicode characters
    homoglyphs = {
        'a': ['à', 'á', 'â'],
        'e': ['è', 'é', 'ê'],
        'i': ['í', 'ì'],
        'o': ['ò', 'ó']
    }
    for i, ch in enumerate(base):
        if ch in homoglyphs:
            for glyph in homoglyphs[ch]:
                new_variant = base[:i] + glyph + base[i+1:]
                variants.add(new_variant + '.' + tld)
    return variants

def generate_bit_flip_variants(domain):
    """Flip one bit in each character (only alphanumeric results kept)."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]
    for i, ch in enumerate(base):
        ascii_val = ord(ch)
        for bit in range(8):
            flipped = ascii_val ^ (1 << bit)
            new_char = chr(flipped)
            if new_char.isalnum():
                new_variant = base[:i] + new_char + base[i+1:]
                variants.add(new_variant + '.' + tld)
    return variants

def generate_keyboard_variants(domain):
    """Simulate keyboard mistakes using QWERTY neighbors."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]
    qwerty_neighbors = {
        'q': ['w', 'a'], 'w': ['q', 'e', 's'], 'e': ['w', 'r', 'd'],
        'r': ['e', 't', 'f'], 't': ['r', 'y', 'g'], 'y': ['t', 'u', 'h'],
        'u': ['y', 'i', 'j'], 'i': ['u', 'o', 'k'], 'o': ['i', 'p', 'l'],
        'p': ['o'], 'a': ['q', 's', 'z'], 's': ['a', 'w', 'd', 'x'],
        'd': ['s', 'e', 'f', 'c'], 'f': ['d', 'r', 'g', 'v'], 'g': ['f', 't', 'h', 'b'],
        'h': ['g', 'y', 'j', 'n'], 'j': ['h', 'u', 'k', 'm'], 'k': ['j', 'i', 'l'],
        'l': ['k', 'o'], 'z': ['a', 'x'], 'x': ['z', 's', 'c'],
        'c': ['x', 'd', 'v'], 'v': ['c', 'f', 'b'], 'b': ['v', 'g', 'n'],
        'n': ['b', 'h', 'm'], 'm': ['n', 'j']
    }
    for i, ch in enumerate(base):
        if ch.lower() in qwerty_neighbors:
            for neighbor in qwerty_neighbors[ch.lower()]:
                replacement = neighbor.upper() if ch.isupper() else neighbor
                new_variant = base[:i] + replacement + base[i+1:]
                variants.add(new_variant + '.' + tld)
    return variants

def generate_tld_variants(domain):
    """Replace the TLD with common alternatives."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, current_tld = parts[0], parts[1]
    common_tlds = ['com', 'net', 'org', 'info', 'biz']
    for tld in common_tlds:
        if tld != current_tld:
            variants.add(base + '.' + tld)
    return variants

def generate_repetition_variants(domain):
    """Simulate accidental extra keystrokes by repeating a character."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]
    for i in range(len(base)):
        new_variant = base[:i] + base[i]*2 + base[i+1:]
        variants.add(new_variant + '.' + tld)
    return variants

def generate_vowel_swap_variants(domain):
    """Swap vowels in the base."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]
    vowels = 'aeiou'
    for i, ch in enumerate(base):
        if ch.lower() in vowels:
            for v in vowels:
                if v != ch.lower():
                    new_variant = base[:i] + (v.upper() if ch.isupper() else v) + base[i+1:]
                    variants.add(new_variant + '.' + tld)
    return variants

def generate_pluralization_variants(domain):
    """Toggle between singular and plural forms."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]
    if base.endswith('s'):
        variants.add(base[:-1] + '.' + tld)
    else:
        variants.add(base + 's' + '.' + tld)
    return variants

def generate_missing_dot_variants(domain):
    """Remove one of the dots (e.g., merging subdomains: www.deepseek.com -> wwwdeepseek.com)."""
    variants = set()
    if domain.count('.') >= 2:
        parts = domain.split('.')
        merged = parts[0] + parts[1] + '.' + parts[2]
        if validate_domain(merged):
            variants.add(merged)
    return variants

def generate_strip_dash_variants(domain):
    """Remove dashes from the base part."""
    variants = set()
    parts = domain.split('.')
    base = parts[0].replace('-', '')
    if base != parts[0]:
        variants.add(base + '.' + parts[1])
    return variants

def generate_common_misspelling_variants(domain):
    """Generate variants based on a misspelling dictionary.
       If a dynamic dictionary was loaded, use that; otherwise, use a default."""
    variants = set()
    parts = domain.split('.')
    if len(parts) < 2:
        raise ValueError("Invalid domain format")
    base, tld = parts[0], parts[1]
    misspellings = MISSPELLING_DICT if MISSPELLING_DICT else {
        "google": ["goggle", "googel", "gugle"],
        "deepseek": ["deepseeek", "deepsek", "depseek"],
    }
    for key, m_list in misspellings.items():
        if base.lower() == key:
            for m in m_list:
                variants.add(m + '.' + tld)
    return variants

def generate_homophone_variants(domain):
    """A basic homophone variant generator (expandable as needed)."""
    variants = set()
    parts = domain.split('.')
    base, tld = parts[0], parts[1]
    homophones = {
        "google": ["gugle"],
        # More homophones can be added here
    }
    if base.lower() in homophones:
        for variant in homophones[base.lower()]:
            variants.add(variant + '.' + tld)
    return variants

def generate_all_variants(domain):
    """Combine all variant generation methods into one unified set."""
    all_variants = set()
    all_variants.update(generate_typo_variants(domain))
    all_variants.update(generate_bit_flip_variants(domain))
    all_variants.update(generate_keyboard_variants(domain))
    all_variants.update(generate_tld_variants(domain))
    all_variants.update(generate_common_misspelling_variants(domain))
    all_variants.update(generate_repetition_variants(domain))
    all_variants.update(generate_vowel_swap_variants(domain))
    all_variants.update(generate_pluralization_variants(domain))
    all_variants.update(generate_missing_dot_variants(domain))
    all_variants.update(generate_strip_dash_variants(domain))
    all_variants.update(generate_homophone_variants(domain))
    return all_variants

#######################################
# Asynchronous Network Functions & Helpers
#######################################

async def async_check_domain_dns(domain, resolver, timeout):
    """Asynchronously check if domain resolves via DNS using aiodns."""
    try:
        await asyncio.wait_for(resolver.query(domain, 'A'), timeout)
        return True
    except Exception:
        return False

async def async_get_http_headers(domain, session, timeout, retries):
    """Asynchronously fetch HTTP headers from a domain."""
    url = 'http://' + domain
    for attempt in range(retries):
        try:
            async with session.get(url, timeout=timeout) as resp:
                return resp.headers
        except Exception:
            if attempt < retries - 1:
                await asyncio.sleep(0.5)
    return None

async def async_check_ssl(domain, timeout, retries):
    """Asynchronously check for a valid SSL certificate."""
    loop = asyncio.get_event_loop()
    ctx = ssl.create_default_context()
    for attempt in range(retries):
        try:
            reader, writer = await asyncio.wait_for(
                asyncio.open_connection(domain, 443, ssl=ctx), timeout
            )
            cert = writer.get_extra_info('ssl_object').getpeercert()
            writer.close()
            await writer.wait_closed()
            return cert
        except Exception:
            if attempt < retries - 1:
                await asyncio.sleep(0.5)
    return None

async def async_get_whois(domain, loop, executor):
    """Run WHOIS lookup in an executor (since whois is synchronous)."""
    try:
        return await loop.run_in_executor(executor, whois.whois, domain)
    except Exception:
        return None

async def async_fetch_content(domain, session, timeout, retries):
    """Fetch page content from a domain asynchronously."""
    url = 'http://' + domain
    for attempt in range(retries):
        try:
            async with session.get(url, timeout=timeout) as resp:
                return await resp.text()
        except Exception:
            if attempt < retries - 1:
                await asyncio.sleep(0.5)
    return None

def compute_levenshtein(s, t):
    """Compute Levenshtein distance (synchronous version)."""
    m, n = len(s), len(t)
    if m == 0: 
        return n
    if n == 0:
        return m
    dp = [[0]*(n+1) for _ in range(m+1)]
    for i in range(m+1):
        dp[i][0] = i
    for j in range(n+1):
        dp[0][j] = j
    for i in range(1, m+1):
        for j in range(1, n+1):
            dp[i][j] = dp[i-1][j-1] if s[i-1]==t[j-1] else 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
    return dp[m][n]

def heuristic_flag(original, variant):
    """Heuristic flag based on edit distance and similarity ratio."""
    original_base = original.split('.')[0]
    variant_base = variant.split('.')[0]
    dist = compute_levenshtein(original_base, variant_base)
    similarity = difflib.SequenceMatcher(None, original_base, variant_base).ratio()
    return dist == 1 or (dist == 2 and similarity > 0.8)

async def compute_fuzzy_similarity(original_hash, domain, session, timeout, retries):
    """Fetch content for a variant and compute ssdeep similarity (if available)."""
    if ssdeep is None or original_hash is None:
        return 0
    content = await async_fetch_content(domain, session, timeout, retries)
    if content:
        variant_hash = ssdeep.hash(content)
        try:
            similarity = ssdeep.compare(original_hash, variant_hash)
            return similarity  # returns a percentage (0-100)
        except Exception:
            return 0
    return 0

async def compute_score(result, original_domain, original_hash, session, timeout, retries, enable_fuzzy):
    """
    Compute a composite score for a variant:
      - Normalized edit distance similarity (up to 30 points)
      - Bonus if heuristic flag is True (50 points)
      - Fuzzy similarity bonus (if enabled; up to 20 points)
      - WHOIS registration age factor (small penalty for older domains)
    """
    score = 0
    orig_base = original_domain.split('.')[0]
    var_base = result["domain"].split('.')[0]
    edit_dist = compute_levenshtein(orig_base, var_base)
    norm_sim = 1 - (edit_dist / max(len(orig_base), 1))
    score += norm_sim * 30

    if result["heuristic_flag"]:
        score += 50

    if enable_fuzzy and ssdeep is not None and original_hash:
        fuzzy_sim = await compute_fuzzy_similarity(original_domain, result["domain"], session, timeout, retries)
        score += (fuzzy_sim / 100) * 20
    else:
        fuzzy_sim = 0

    whois_info = result.get("whois")
    if whois_info and hasattr(whois_info, 'creation_date'):
        try:
            creation = whois_info.creation_date
            if isinstance(creation, list):
                creation = creation[0]
            age_days = (datetime.datetime.now() - creation).days
            penalty = min(age_days / 365, 5) * 2
            score -= penalty
        except Exception:
            pass

    result["score"] = round(score, 2)
    return result

#######################################
# Asynchronous Variant Processing
#######################################

async def process_variant_async(variant, original, session, resolver, loop, executor,
                                semaphore, timeout, retries, enable_fuzzy, original_hash):
    async with semaphore:
        result = {"domain": variant}
        result["dns_active"] = await async_check_domain_dns(variant, resolver, timeout)
        result["whois"] = await async_get_whois(variant, loop, executor)
        result["ssl_cert"] = await async_check_ssl(variant, timeout, retries)
        result["http_headers"] = await async_get_http_headers(variant, session, timeout, retries)
        result["heuristic_flag"] = heuristic_flag(original, variant)
        result["popularity"] = "Unknown"
        result = await compute_score(result, original, original_hash, session, timeout, retries, enable_fuzzy)
        return result

#######################################
# Output Functions
#######################################

def print_results(results):
    """Print the analysis results for each domain variant."""
    for res in results:
        print("-" * 40)
        print("Domain:", res["domain"])
        print(" - DNS Active:", res["dns_active"])
        print(" - WHOIS Data:", "Available" if res["whois"] else "Not available")
        print(" - SSL Certificate:", "Present" if res["ssl_cert"] else "Not available")
        print(" - HTTP Headers:", "Present" if res["http_headers"] else "Not available")
        print(" - Heuristic Flag:", res["heuristic_flag"])
        print(" - Estimated Popularity:", res["popularity"])
        print(" - Composite Score:", res.get("score", 0))
    print("-" * 40)

def write_true_positives(results):
    """Write the true positive variants (flagged by heuristic) to TP.txt along with count."""
    true_positives = [res for res in results if res["heuristic_flag"]]
    count = len(true_positives)
    with open("TP.txt", "w") as f:
        f.write(f"Total True Positives: {count}\n")
        f.write("=" * 40 + "\n")
        for res in true_positives:
            f.write("-" * 40 + "\n")
            f.write("Domain: " + res["domain"] + "\n")
            f.write(" - DNS Active: " + str(res["dns_active"]) + "\n")
            f.write(" - WHOIS Data: " + ("Available" if res["whois"] else "Not available") + "\n")
            f.write(" - SSL Certificate: " + ("Present" if res["ssl_cert"] else "Not available") + "\n")
            f.write(" - HTTP Headers: " + ("Present" if res["http_headers"] else "Not available") + "\n")
            f.write(" - Heuristic Flag: " + str(res["heuristic_flag"]) + "\n")
            f.write(" - Estimated Popularity: " + res["popularity"] + "\n")
            f.write(" - Composite Score: " + str(res.get("score", 0)) + "\n")
        f.write("-" * 40 + "\n")
    print("True positive results written to TP.txt")

def final_summary(results):
    """Print a final summary of the analysis, explaining true positive classification."""
    true_positives_dns = [res for res in results if res["dns_active"]]
    count_dns_active = len(true_positives_dns)
    true_positives_flagged = [res for res in results if res["heuristic_flag"]]
    count_flagged = len(true_positives_flagged)
    
    print("\nSummary:")
    print("=" * 40)
    print(f"Total variants evaluated: {len(results)}")
    print(f" - Variants active (DNS found): {count_dns_active}")
    print(f" - Variants flagged as suspicious (heuristic true positives): {count_flagged}")
    print("\n1. Initial filter: Identify domains that are active (DNS status 'active').")
    print("2. Further analysis should combine:")
    print("    - Registration/DNS status (e.g., active status and any registration anomalies)")
    print("    - Detailed WHOIS/SSL analysis (e.g., mismatched SSL certificates, privacy-protected WHOIS)")
    print("    - Content similarity (using fuzzy hashing such as ssdeep/TLSH)")
    print("    - Network traffic indicators (correlating with logs and SIEM alerts)")
    print("=" * 40)

#######################################
# Main Asynchronous Analysis and CLI
#######################################

def validate_domain(domain):
    """Validate the domain format using a regex."""
    pattern = r"^(?:[a-zA-Z0-9-]+\.)+[a-zA-Z]{2,}$"
    return re.match(pattern, domain) is not None

async def main_async():
    parser = argparse.ArgumentParser(description="Advanced Asynchronous Typosquatting Detection Tool")
    parser.add_argument("-d", "--domain", help="Original domain (e.g., deepseek.com)")
    parser.add_argument("--timeout", type=float, default=3.0, help="Timeout for network requests (seconds)")
    parser.add_argument("--retries", type=int, default=2, help="Number of retries for network requests")
    parser.add_argument("--max-concurrent", type=int, default=10, help="Maximum concurrent network requests")
    parser.add_argument("--enable-fuzzy", action="store_true", help="Enable fuzzy (ssdeep) content similarity checks")
    parser.add_argument("--misspelling-file", help="File path for dynamic misspelling dictionary (CSV: key,misspelling1,misspelling2,...)")
    args, unknown = parser.parse_known_args()

    if args.domain:
        original_domain = args.domain.strip()
    else:
        original_domain = input("Enter the original domain (e.g., deepseek.com): ").strip()

    if not validate_domain(original_domain):
        print("Invalid domain format. Please provide a valid domain (e.g., deepseek.com).")
        return

    # Load dynamic misspelling dictionary if provided
    global MISSPELLING_DICT
    if args.misspelling_file:
        try:
            with open(args.misspelling_file, "r") as f:
                for line in f:
                    parts = line.strip().split(',')
                    if parts:
                        key = parts[0].strip().lower()
                        MISSPELLING_DICT[key] = [x.strip() for x in parts[1:] if x.strip()]
        except Exception as e:
            print(f"Error loading misspelling file: {e}")

    print(f"Generating variants for {original_domain} ...")
    variants = generate_all_variants(original_domain)
    print(f"Total variants generated: {len(variants)}")

    timeout = args.timeout
    retries = args.retries
    semaphore = asyncio.Semaphore(args.max_concurrent)
    resolver = aiodns.DNSResolver()
    async with aiohttp.ClientSession() as session:
        loop = asyncio.get_event_loop()
        executor = concurrent.futures.ThreadPoolExecutor(max_workers=5)

        # If fuzzy checks are enabled and ssdeep is available, fetch original content and compute hash
        original_hash = None
        if args.enable_fuzzy and ssdeep is not None:
            orig_content = await async_fetch_content(original_domain, session, timeout, retries)
            if orig_content:
                original_hash = ssdeep.hash(orig_content)
            else:
                print("Could not fetch content from original domain for fuzzy checks.")

        tasks = []
        for variant in variants:
            tasks.append(process_variant_async(variant, original_domain, session, resolver, loop, executor,
                                                 semaphore, timeout, retries, args.enable_fuzzy, original_hash))
        results = await asyncio.gather(*tasks)

    print_results(results)
    true_positive_count = len([res for res in results if res["heuristic_flag"]])
    print(f"\nTotal true positives (based on heuristic flag): {true_positive_count}")
    write_true_positives(results)
    final_summary(results)

def main():
    # For environments (like Jupyter) with a running event loop, consider using nest_asyncio:
    # import nest_asyncio; nest_asyncio.apply()
    asyncio.run(main_async())

if __name__ == "__main__":
    main()
